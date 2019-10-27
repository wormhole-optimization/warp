use egg::{
    define_term,
    egraph::EClass,
    expr::{Expr, Language},
};

use std::collections::HashMap;
use std::i32;
use std::hash::Hash;
use std::cmp::min;

use ordered_float::NotNan;

mod rules;
pub use rules::{rules, trans_rules, untrans_rules};

mod extract;
pub use extract::*;

pub type EGraph = egg::egraph::EGraph<Math, Meta>;

type Number = i32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    schema:   Option<Schema>,
    sparsity: Option<NotNan<f64>>,
    nnz:      Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Schema {
    Schm(HashMap<String, usize>),
    Dims(String, usize),
    Name(String),
    Size(usize),
    Mat(usize, usize),
}

impl Schema {
    pub fn union(&self, other: &Self) -> Self {
        if let (Self::Schm(s1), Self::Schm(s2)) = (self, other) {
            let mut res = s1.clone();
            res.extend(s2.clone());
            Self::Schm(res)
        } else {
            panic!("unioning a non-schema")
        }
    }
}

impl egg::egraph::Metadata<Math> for Meta {
    type Error = std::convert::Infallible;

    fn modify(_eclass: &mut EClass<Math, Self>) {}
    fn merge(&self, other: &Self) -> Self {

        let sparsity = match &self.sparsity {
            None => other.sparsity,
            Some(s1) => match &other.sparsity {
                None => Some(*s1),
                Some(s2) => Some(*min(s1, s2))
            }
        };

        let nnz = match &self.nnz {
            None => other.nnz,
            Some(n1) => match &other.nnz {
                None => Some(*n1),
                Some(n2) => Some(*min(n1, n2))
            }
        };

        let schema = match (&sparsity, &nnz)  {
            (Some(f), Some(0)) => {
                if *f == NotNan::from(0 as f64) {
                    Some(Schema::Schm(HashMap::new()))
                } else  {
                    assert_eq!(&self.schema, &other.schema,
                               "merging expressions with different schema");
                    self.schema.clone()
                }
            },
            _ => {
                assert_eq!(&self.schema, &other.schema,
                           "merging expressions with different schema");
                self.schema.clone()
            }
        };

        Meta {schema, sparsity, nnz}
    }

    fn make(expr: Expr<Math, &Self>) -> Self {
        use Math::*;
        let schema = match expr.op {
            Add => {
                // schema: union
                // sparsity: sum
                // nnz: calculate from sparsity
                assert_eq!(expr.children.len(), 2, "wrong length in add");
                let x = &expr.children[0];
                let y = &expr.children[1];

                let x_schema = x.schema.as_ref()
                    .expect("wrong schema in argument to add");
                let y_schema = y.schema.as_ref()
                    .expect("wrong schema in argument to add");

                let schema = Some(x_schema.union(&y_schema));

                let sparsity =
                    if let (Some(x_s), Some(y_s)) = (x.sparsity, y.sparsity) {
                        Some(min(NotNan::from(1 as f64), x_s + y_s))
                    } else {
                        //panic!("no sparsity in agument to add")
                        None
                    };

                let nnz = if let Some(Schema::Schm(sch)) = &schema {
                    let vol: usize = sch.values().product();
                    match sparsity {
                        Some(sp) => {
                            let nnz = NotNan::from(vol as f64) * sp;
                            Some(nnz.round() as usize)
                        },
                        //_ => panic!("impossible")
                        _=>None
                    }
                } else {
                    unreachable!()
                };

                Meta {schema, sparsity, nnz}
            },
            Mul => {
                // schema: union
                // sparsity: min
                // nnz: calculate from sparsity
                assert_eq!(expr.children.len(), 2, "wrong length in mul");
                let x = &expr.children[0];
                let y = &expr.children[1];

                let x_schema = x.schema.as_ref()
                    .expect("wrong schema in argument to mul");
                let y_schema = y.schema.as_ref()
                    .expect("wrong schema in argument to mul");

                let schema = Some(x_schema.union(&y_schema));

                let sparsity =
                    if let (Some(x_s), Some(y_s)) = (x.sparsity, y.sparsity) {
                        Some(min(x_s, y_s))
                    } else {
                        //panic!("no sparsity in agument to mul")
                        None
                    };

                let nnz = if let Some(Schema::Schm(sch)) = &schema {
                    let vol: usize = sch.values().product();
                    match sparsity {
                        Some(sp) => {
                            let nnz = NotNan::from(vol as f64) * sp;
                            Some(nnz.round() as usize)
                        },
                        //_ => panic!("impossible")
                        _ => None
                    }
                } else {
                    unreachable!()
                };

                Meta {schema, sparsity, nnz}
            },
            Agg => {
                // schema: remove summed dim
                // sparsity: calculate
                // nnz: calculate from sparsity
                assert_eq!(expr.children.len(), 2, "wrong length in sum");
                let dim = &expr.children[0];
                let body = &expr.children[1];

                let (k, mut body_schema) =
                    if let (Schema::Dims(i,n), Schema::Schm(schema)) =
                    (&dim.schema.as_ref().unwrap(), &body.schema.as_ref().unwrap()) {
                        (i, schema.clone())
                    } else {
                        panic!("wrong schema in aggregate")
                    };

                body_schema.remove(k);

                let vol = body_schema.values().product();
                let schema = Some(Schema::Schm(body_schema));
                let sparsity = body.nnz.map(|nnz| {
                    min(
                        NotNan::from(1 as f64),
                        NotNan::from(nnz as f64) / NotNan::from(vol as f64)
                    )
                });
                let nnz = body.nnz.map(|z| {
                    min(vol, z)
                });

                Meta {schema, sparsity, nnz}
            },
            Lit => {
                //    schema: empty
                //    sparsity: 1/0
                //    nnz: 1/0
                let num = &expr.children[0];
                Meta {
                    schema: Some(Schema::Schm(HashMap::default())),
                    sparsity: num.sparsity,
                    nnz: num.nnz
                }
            },
            Mat => {
                //    schema: schema
                //    sparsity: sparsity
                //    nnz: nnz
                assert_eq!(expr.children.len(), 4, "wrong length in matrix");
                let i_schema = &expr.children[1];
                let j_schema = &expr.children[2];
                let nnz = &expr.children[3].nnz;

                let (schema, n, m) =
                    if let (Some(Schema::Dims(i, n)), Some(Schema::Dims(j, m))) =
                    (&i_schema.schema, &j_schema.schema) {
                    let res: HashMap<_,_> = vec![(i.clone(), *n), (j.clone(), *m)]
                        .into_iter().collect();
                    (Schema::Schm(res), n, m)
                } else {
                    panic!("wrong schema in matrix")
                };

                Meta {
                    schema: Some(schema),
                    nnz: *nnz,
                    sparsity: Some(NotNan::from(nnz.unwrap() as f64 / (n * m) as f64))
                }
            },
            Dim => {
                //    schema: dims
                //    sparsity: None
                //    nnz: none
                assert_eq!(expr.children.len(), 2, "wrong length in dim");
                let i = &expr.children[0];
                let n = &expr.children[1];
                let schema =
                    if let (Some(Schema::Name(i)), Some(Schema::Size(n))) =
                    (&i.schema, &n.schema) {
                    Schema::Dims(i.clone(), *n)
                } else {
                    panic!("wrong schema in dim {:?}", (i, n))
                };

                Meta {
                    schema: Some(schema),
                    nnz: None,
                    sparsity: None
                }
            },
            Sub => {
                //    schema: substitute
                //    sparsity: same
                //    nnz: same
                assert_eq!(expr.children.len(), 3, "wrong length in subst");
                let e = &expr.children[0];
                let v = &expr.children[1];
                let body = &expr.children[2];

                let (e_i, e_n) = if let Some(Schema::Dims(i, n)) = &e.schema {
                    (i, n)
                } else {
                    panic!("wrong schema in subst e")
                };

                let (v_i, v_n) = if let Some(Schema::Dims(i, n)) = &v.schema {
                    (i, n)
                } else {
                    panic!("wrong schema in subst v")
                };

                let schema = match &body.schema.as_ref().unwrap() {
                    Schema::Schm(schema) => {
                        let mut res = schema.clone();
                        if let Some(m) = res.remove(v_i) {
                            res.insert(e_i.clone(), m);
                        }
                        Schema::Schm(res)
                    },
                    Schema::Dims(body_i, body_n) => {
                        if body_i == v_i {
                            Schema::Dims(e_i.clone(), *e_n)
                        } else {
                            Schema::Dims(body_i.clone(), *body_n)
                        }
                    },
                    _ => panic!("cannot subst for attr. and size")
                };

                Meta {
                    schema: Some(schema),
                    nnz: body.nnz,
                    sparsity: body.sparsity
                }
            },
            Var => {
                //    schema: empty
                //    sparsity: 0
                //    nnz: 1
                Meta {
                    schema: Some(Schema::Schm(HashMap::default())),
                    nnz: Some(1),
                    sparsity: Some(NotNan::from(0 as f64))
                }
            },
            Num(n) => {
                //    schema: Size
                //    sparsity: 0/1
                //    nnz: 0/1
                Meta {
                    schema: Some(Schema::Size(n as usize)),
                    nnz: Some(if n == 0 { 0 } else { 1 }),
                    sparsity: Some(
                        if n == 0 {
                            NotNan::from(0 as f64)
                        } else {
                            NotNan::from(1 as f64)
                        }
                    )
                }
            },
            Nnz => {
                //    schema: None
                //    sparsity: None
                //    nnz: nnz
                let n = &expr.children[0].schema;

                let nnz = if let Some(Schema::Size(nnz)) = n {
                    Some(*nnz)
                } else {
                    panic!("wrong schema in nnz")
                };
                Meta {
                    schema: None,
                    nnz: nnz,
                    sparsity: None,
                }
            },
            Str(s) => {
                //    schema: Some(Name)
                //    sparsity: 0
                //    nnz: 1
                Meta {
                    schema: Some(Schema::Name(s)),
                    nnz: Some(1),
                    sparsity: Some(NotNan::from(1 as f64))
                }
            },
            // Schema rules for LA plans
            LMat => {
                assert_eq!(expr.children.len(), 4, "wrong length in lmat");
                let i_schema = &expr.children[1].schema;
                let j_schema = &expr.children[2].schema;
                let nnz = &expr.children[3].nnz;

                let (row, col) = if let (Some(Schema::Size(r)), Some(Schema::Size(c)))
                    = (i_schema, j_schema) {
                        (r, c)
                    } else {
                        panic!("wrong schema in lmat")
                    };

                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: *nnz,
                    sparsity: None
                }
            },
            LMin => {
                assert_eq!(expr.children.len(), 2, "wrong length in lmin");
                let x_schema = &expr.children[0].schema;
                let y_schema = &expr.children[1].schema;

                let (x_i, x_j, y_i, y_j) =
                    if let (Some(Schema::Mat(xrow, xcol)), Some(Schema::Mat(yrow, ycol)))
                    = (x_schema, y_schema) {
                        (xrow, xcol, yrow, ycol)
                    } else {
                        panic!("wrong schema in lmin")
                    };

                assert!(
                    (x_i == y_i && x_j == y_j)
                        || (x_i == y_i && *y_i == 1)
                        || (x_i == y_i && *x_i == 1)
                        || (*x_i == 1 && x_j == y_j)
                        || (*y_i == 1 && x_j == y_j)
                        || (*x_i == 1 && *x_j == 1)
                        || (*y_i == 1 && *y_j == 1)
                );
                let row = if *x_i == 1 { y_i } else { x_i };
                let col = if *x_j == 1 { y_j } else { x_j };

                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: None,
                    sparsity: None
                }
            },
            LAdd => {
                assert_eq!(expr.children.len(), 2, "wrong length in ladd");
                let x_schema = &expr.children[0].schema;
                let y_schema = &expr.children[1].schema;

                let (x_i, x_j, y_i, y_j) =
                    if let (Some(Schema::Mat(xrow, xcol)), Some(Schema::Mat(yrow, ycol)))
                    = (x_schema, y_schema) {
                        (xrow, xcol, yrow, ycol)
                    } else {
                        panic!("wrong schema in ladd")
                    };

                assert!(
                    (x_i == y_i && x_j == y_j)
                        || (x_i == y_i && *y_i == 1)
                        || (x_i == y_i && *x_i == 1)
                        || (*x_i == 1 && x_j == y_j)
                        || (*y_i == 1 && x_j == y_j)
                        || (*x_i == 1 && *x_j == 1)
                        || (*y_i == 1 && *y_j == 1)
                );
                let row = if *x_i == 1 { y_i } else { x_i };
                let col = if *x_j == 1 { y_j } else { x_j };

                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: None,
                    sparsity: None
                }
            },
            LMul => {
                assert_eq!(expr.children.len(), 2, "wrong length in lmul");
                let x_schema = &expr.children[0].schema;
                let y_schema = &expr.children[1].schema;

                let (x_i, x_j, y_i, y_j) =
                    if let (Some(Schema::Mat(xrow, xcol)), Some(Schema::Mat(yrow, ycol)))
                    = (x_schema, y_schema) {
                        (xrow, xcol, yrow, ycol)
                    } else {
                        panic!("wrong schema in lmul {:?} {:?}", x_schema, y_schema)
                    };

                assert!(
                    (x_i == y_i && x_j == y_j)
                        || (x_i == y_i && *y_i == 1)
                        || (x_i == y_i && *x_i == 1)
                        || (*x_i == 1 && x_j == y_j)
                        || (*y_i == 1 && x_j == y_j)
                        || (*x_i == 1 && *x_j == 1)
                        || (*y_i == 1 && *y_j == 1)
                );
                let row = if *x_i == 1 { y_i } else { x_i };
                let col = if *x_j == 1 { y_j } else { x_j };

                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: None,
                    sparsity: None
                }
            },
            MMul => {
                assert_eq!(expr.children.len(), 2, "wrong length in mmul");
                let x_schema = &expr.children[0].schema;
                let y_schema = &expr.children[1].schema;

                let (x_i, x_j, y_i, y_j) =
                    if let (Some(Schema::Mat(xrow, xcol)), Some(Schema::Mat(yrow, ycol)))
                    = (x_schema, y_schema) {
                        (xrow, xcol, yrow, ycol)
                    } else {
                        panic!("wrong schema in mmul")
                    };

                assert_eq!(*x_j, *y_i, "wrong dimensions in mmul");

                Meta {
                    schema: Some(Schema::Mat(*x_i, *y_j)),
                    nnz: None,
                    sparsity: None
                }
            },
            LTrs => {
                assert_eq!(expr.children.len(), 1, "wrong length in transpose");
                let x_schema = &expr.children[0].schema;

                let (x_i, x_j) = if let Some(Schema::Mat(row, col)) = x_schema {
                    (row, col)
                } else {
                    panic!("wrong schema in transpose")
                };

                Meta {
                    schema: Some(Schema::Mat(*x_j , *x_i)),
                    nnz: None,
                    sparsity: None
                }
            },
            Srow => {
                assert_eq!(expr.children.len(), 1, "wrong length in transpose");
                let x_schema = &expr.children[0].schema;

                let (x_i, _x_j) = if let Some(Schema::Mat(row, col)) = x_schema {
                    (row, col)
                } else {
                    panic!("wrong schema in transpose")
                };

                Meta {
                    schema: Some(Schema::Mat(*x_i , 1)),
                    nnz: None,
                    sparsity: None
                }
            },
            Scol => {
                assert_eq!(expr.children.len(), 1, "wrong length in transpose");
                let x_schema = &expr.children[0].schema;

                let (_x_i, x_j) = if let Some(Schema::Mat(row, col)) = x_schema {
                    (row, col)
                } else {
                    panic!("wrong schema in transpose")
                };

                Meta {
                    schema: Some(Schema::Mat(1, *x_j)),
                    nnz: None,
                    sparsity: None
                }
            },
            Sall => {
                Meta {
                    schema: Some(Schema::Mat(1, 1)),
                    nnz: None,
                    sparsity: None
                }
            },
            Bind => {
                assert_eq!(expr.children.len(), 3, "wrong length in lmat");
                let i_schema = &expr.children[0].schema;
                let j_schema = &expr.children[1].schema;
                let x_schema = &expr.children[2].schema;

                let (i, j) = if let (Some(Schema::Name(i)), Some(Schema::Name(j))) =
                    (i_schema, j_schema) {
                        (i, j)
                    } else {
                        panic!("wrong schema in bind")
                    };

                let (x_row, x_col) = if let Some(Schema::Mat(row, col)) = x_schema {
                    (row, col)
                } else {
                    panic!("wrong schema in bind")
                };

                let mut schema = HashMap::new();

                if *x_row != 1 {
                    schema.insert(i.clone(), *x_row);
                }

                if *x_col != 1 {
                    schema.insert(j.clone(), *x_col);
                }

                Meta {
                    schema: Some(Schema::Schm(schema)),
                    nnz: None,
                    sparsity: None
                }
            },
            Ubnd => {
                assert_eq!(expr.children.len(), 3, "wrong length in ubind");
                let i_schema = &expr.children[0].schema;
                let j_schema = &expr.children[1].schema;
                let x_schema = &expr.children[2].schema;

                let (i, j) = if let (Some(Schema::Name(i)), Some(Schema::Name(j))) =
                    (i_schema, j_schema) {
                        (i, j)
                    } else {
                        panic!("wrong schema in unbind")
                    };

                let x_s = if let Some(Schema::Schm(s)) = x_schema {
                    s
                } else {
                    panic!("wrong schema in unbind x: {:?}", x_schema)
                };

                let row = if i == "_" {1} else {*x_s.get(i).unwrap()};
                let col = if j == "_" {1} else {*x_s.get(j).unwrap()};

                Meta {
                    schema: Some(Schema::Mat(row, col)),
                    nnz: None,
                    sparsity: None
                }
            },
            LLit => {
                assert_eq!(expr.children.len(), 1, "wrong length in lmat");

                Meta {
                    schema: Some(Schema::Mat(1, 1)),
                    nnz: None,
                    sparsity: None
                }
            }
        };
        schema
    }
}

define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub enum Math {
        LMat = "lmat",
        LAdd = "l+",
        LMin = "l-",
        LMul = "l*",
        MMul = "m*",
        LTrs = "trans",
        Srow = "srow",
        Scol = "scol",
        Sall = "sall",
        Bind = "b+",
        Ubnd = "b-",
        LLit = "llit",

        Add = "+",
        // schema: union
        // sparsity: sum
        // nnz: calculate from sparsity
        Mul = "*",
        // schema: union
        // sparsity: min
        // nnz: calculate from sparsity
        Agg = "sum",
        // schema: remove summed dim
        // sparsity: calculate
        // nnz: calculate from sparsity
        Lit = "lit",
        //    schema: empty
        //    sparsity: 1/0
        //    nnz: 1/0
        Var = "var",
        //    schema: empty
        //    sparsity: 0
        //    nnz: 1
        Mat = "mat",
        //    schema: schema
        //    sparsity: sparsity
        //    nnz: nnz
        Dim = "dim",
        //    schema: dims
        //    sparsity: None
        //    nnz: none
        Nnz = "nnz",
        //    schema: None
        //    sparsity: None
        //    nnz: nnz
        Sub = "subst",
        //    schema: substitute
        //    sparsity: same
        //    nnz: same
        Num(Number),
        //    schema: Size
        //    sparsity: 0/1
        //    nnz: 0/1
        Str(String),
        //    schema: Some(Name)
        //    sparsity: 0
        //    nnz: 1
    }
}

impl Language for Math {
    fn cost(&self, _children: &[u64]) -> u64 {
        use Math::*;
        match self {
            LMat | LAdd | LMin | LMul |
            MMul | LTrs | Srow | Scol |
            Sall | Bind | Ubnd | LLit |
            Sub => 1,
            _ => 0
        }
    }
}
