use egg::{
    define_term,
    egraph::EClass,
    expr::{Expr, Language},
};

use std::collections::HashMap;
use std::i32;
use std::hash::Hash;

use ordered_float::NotNan;

mod rules;
pub use rules::rules;

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
                None => Some(s1.clone()),
                Some(s2) => Some(std::cmp::min(s1, s2).clone())
            }
        };

        let nnz = match &self.nnz {
            None => other.nnz,
            Some(n1) => match &other.nnz {
                None => Some(*n1),
                Some(n2) => Some(std::cmp::min(n1, n2).clone())
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
        let schema = match expr.op {
            Math::Add => {
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
                        Some(std::cmp::min(NotNan::from(1 as f64), x_s + y_s))
                    } else {
                        panic!("no sparsity in agument to add")
                    };

                let nnz = if let Some(Schema::Schm(sch)) = &schema {
                    let vol: usize = sch.values().product();
                    match sparsity {
                        Some(sp) => {
                            NotNan::from(vol as f64) * sp
                        },
                        _ => panic!("impossible")
                    }
                } else {
                    panic!("impossible")
                };

                Meta {schema, sparsity, nnz: Some(nnz.round() as usize)}
            },
            Math::Mul => {
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
                        Some(std::cmp::min(x_s, y_s))
                    } else {
                        panic!("no sparsity in agument to mul")
                    };

                let nnz = if let Some(Schema::Schm(sch)) = &schema {
                    let vol: usize = sch.values().product();
                    match sparsity {
                        Some(sp) => {
                            NotNan::from(vol as f64) * sp
                        },
                        _ => panic!("impossible")
                    }
                } else {
                    panic!("impossible")
                };

                Meta {schema, sparsity, nnz: Some(nnz.round() as usize) }
            },
            Math::Agg => {
                // schema: remove summed dim
                // sparsity: calculate
                // nnz: calculate from sparsity
                assert_eq!(expr.children.len(), 2, "wrong length in sum");
                let dim = &expr.children[0];
                let body = &expr.children[1];

                let (k, mut body_schema) =
                    if let (Some(Schema::Dims(i,n)), Some(Schema::Schm(schema))) =
                    (&dim.schema, &body.schema) {
                        (i, schema.clone())
                    } else {
                        panic!("wrong schema in aggregate")
                    };
                body_schema.remove(k);
                let schema = Schema::Schm(body_schema);

                let sparsity = if let Schema::Schm(s) = &schema {
                    let vol: usize = s.values().product();
                    Some(
                        std::cmp::min(
                            NotNan::from(1 as f64),
                            NotNan::from(body.nnz.unwrap() as f64) / NotNan::from(vol as f64)
                        )
                    )
                } else {
                    panic!("impossible")
                };

                Meta {schema: Some(schema), sparsity, nnz: body.nnz}
            },
            Math::Lit => {
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
            Math::Mat => {
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
            Math::Dim => {
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
            Math::Sub => {
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
            Math::Var => {
                //    schema: empty
                //    sparsity: 0
                //    nnz: 1
                Meta {
                    schema: Some(Schema::Schm(HashMap::default())),
                    nnz: Some(1),
                    sparsity: Some(NotNan::from(0 as f64))
                }
            },
            Math::Num(n) => {
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
            Math::Nnz => {
                //    schema: None
                //    sparsity: None
                //    nnz: nnz
                let nnz = &expr.children[0].nnz;
                Meta {
                    schema: None,
                    nnz: *nnz,
                    sparsity: None,
                }
            },
            Math::Str(s) => {
                //    schema: Some(Name)
                //    sparsity: 0
                //    nnz: 1
                Meta {
                    schema: Some(Schema::Name(s)),
                    nnz: Some(1),
                    sparsity: Some(NotNan::from(1 as f64))
                }
            },
            _ => Meta {schema: None, nnz: None, sparsity: None}
        };
        schema
    }

}

//pub struct Meta {
//}
//
//#[derive(Debug, Clone, PartialEq, Eq)]
//pub enum Schema {
//    Schema(HashMap<String, usize>),
//    Dims(String, usize),
//    Name(String),
//    Size(usize),
//    Unit
//}

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
    fn cost(&self, children: &[u64]) -> u64 {
        let s:u64 = children.iter().sum();
        1 + s
    }
}
