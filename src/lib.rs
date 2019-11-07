use egg::{
    define_term,
    egraph::EClass,
    expr::{Expr, Language},
};

use std::collections::HashMap;
use std::i32;
use std::hash::Hash;
use std::cmp::min;
use std::iter::*;

use ordered_float::NotNan;

mod hop;
pub use hop::*;

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
    pub fn get_schm(&self) -> &HashMap<String, usize> {
        if let Self::Schm(s) = self {
            s
        } else {
            panic!("cannot get schm")
        }
    }

    pub fn get_dims(&self) -> (&String, &usize) {
        if let Self::Dims(i, n) = self {
            (i, n)
        } else {
            panic!("cannot get dims")
        }
    }

    pub fn get_name(&self) -> &String {
        if let Self::Name(n) = self {
            n
        } else {
            panic!("cannot get name")
        }
    }

    pub fn get_size(&self) -> &usize {
        if let Self::Size(s) = self {
            s
        } else {
            panic!("cannot get size")
        }
    }

    pub fn get_mat(&self) -> (&usize, &usize) {
        if let Self::Mat(i, j) = self {
            (i, j)
        } else {
            panic!("cannot get mat")
        }
    }

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
        let sparsity = [self.sparsity, other.sparsity]
            .into_iter().flatten().min().copied();
        let nnz = [self.nnz, other.nnz]
            .into_iter().flatten().min().copied();
        let schema = match (&sparsity, &nnz)  {
            (Some(f), Some(0)) if *f == 0.0.into() => {
                    Some(Schema::Schm(HashMap::new()))
            },
            _ => {
                debug_assert_eq!(&self.schema, &other.schema);
                self.schema.clone()
            }
        };
        Meta {schema, sparsity, nnz}
    }

    fn make(expr: Expr<Math, &Self>) -> Self {
        use Math::*;
        let schema = match expr.op {
            Add => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in add");
                let x = &expr.children[0];
                let y = &expr.children[1];

                let mut schema = x.schema.as_ref().unwrap().get_schm().clone();
                let y_schema = y.schema.as_ref().unwrap().get_schm().clone();
                schema.extend(y_schema);

                let sparsity = x.sparsity.and_then(|x| y.sparsity.map(|y| {
                        min(1.0.into(), x + y)
                }));

                let nnz = sparsity.map(|sp| {
                    let vol: usize = schema.values().product();
                    let nnz = NotNan::from(vol as f64) * sp;
                    nnz.round() as usize
                });

                let schema = Some(Schema::Schm(schema));

                Meta {schema, sparsity, nnz}
            },
            Mul => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in mul");
                let x = &expr.children[0];
                let y = &expr.children[1];

                let mut schema = x.schema.as_ref().unwrap().get_schm().clone();
                let y_schema = y.schema.as_ref().unwrap().get_schm().clone();
                schema.extend(y_schema);

                let sparsity = min(x.sparsity, y.sparsity);

                let nnz = sparsity.map(|sp| {
                    let vol: usize = schema.values().product();
                    let nnz = NotNan::from(vol as f64) * sp;
                    nnz.round() as usize
                });

                let schema = Some(Schema::Schm(schema));

                Meta {schema, sparsity, nnz}
            },
            Agg => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in sum");
                let body = &expr.children[1];

                let k = expr_schema(&expr, 0).get_dims().0;
                let mut body_schema = body.schema.as_ref().unwrap().get_schm().clone();
                body_schema.remove(k);

                let vol = body_schema.values().product();
                let sparsity = body.nnz.map(|nnz| { min(
                    1.0.into(),
                    NotNan::from(nnz as f64 / vol as f64)
                )});
                let nnz = body.nnz.map(|z| min(vol, z));

                let schema = Some(Schema::Schm(body_schema));

                Meta {schema, sparsity, nnz}
            },
            Lit => {
                let num = &expr.children[0];
                Meta {
                    schema: Some(Schema::Schm(HashMap::default())),
                    sparsity: num.sparsity,
                    nnz: num.nnz
                }
            },
            Mat => {
                debug_assert_eq!(expr.children.len(), 4, "wrong length in matrix");
                let (i, n) = expr_schema(&expr, 1).get_dims();
                let (j, m) = expr_schema(&expr, 2).get_dims();

                let mut schema = HashMap::new();
                if *n != 1 {
                    schema.insert(i.clone(), *n);
                }
                if *m != 1 {
                    schema.insert(j.clone(), *m);
                };

                let nnz = expr.children[3].nnz;

                Meta {
                    schema: Some(Schema::Schm(schema)),
                    nnz,
                    sparsity: Some(NotNan::from(nnz.unwrap() as f64 / (n * m) as f64))
                }
            },
            Dim => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in dim");
                let schema = Schema::Dims(
                    expr_schema(&expr, 0).get_name().clone(),
                    *expr_schema(&expr, 1).get_size(),
                );
                Meta {
                    schema: Some(schema),
                    nnz: None,
                    sparsity: None
                }
            },
            Sub => {
                debug_assert_eq!(expr.children.len(), 3, "wrong length in subst");
                let (e_i, e_n) = expr_schema(&expr, 0).get_dims();
                let (v_i, v_n) = expr_schema(&expr, 1).get_dims();
                debug_assert_eq!(e_n, v_n, "substituting for different size");
                let body = &expr.children[2];

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
                Meta {
                    schema: Some(Schema::Schm(HashMap::default())),
                    nnz: Some(1),
                    sparsity: Some(1.0.into())
                }
            },
            Num(n) => {
                Meta {
                    schema: Some(Schema::Size(n as usize)),
                    nnz: Some(if n == 0 { 0 } else { 1 }),
                    sparsity: Some(if n == 0 {0.0.into()} else {1.0.into()})
                }
            },
            Nnz => {
                let n = expr_schema(&expr, 0).get_size();
                Meta {
                    schema: None,
                    nnz: Some(*n),
                    sparsity: None,
                }
            },
            Str(s) => {
                Meta {
                    schema: Some(Schema::Name(s)),
                    nnz: Some(1),
                    sparsity: Some(1.0.into())
                }
            },
            // Schema rules for LA plans
            LMat => {
                debug_assert_eq!(expr.children.len(), 4, "wrong length in lmat");
                let row = expr_schema(&expr, 1).get_size();
                let col = expr_schema(&expr, 2).get_size();
                let nnz = &expr.children[3].nnz;
                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: *nnz,
                    sparsity: None
                }
            },
            LMin => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in lmin");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                let (y_i, y_j) = expr_schema(&expr, 1).get_mat();
                dims_ok(*x_i, *x_j, *y_i, *y_j);
                let row = if *x_i == 1 { y_i } else { x_i };
                let col = if *x_j == 1 { y_j } else { x_j };
                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: None,
                    sparsity: None
                }
            },
            LAdd => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in ladd");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                let (y_i, y_j) = expr_schema(&expr, 1).get_mat();
                dims_ok(*x_i, *x_j, *y_i, *y_j);
                let row = if *x_i == 1 { y_i } else { x_i };
                let col = if *x_j == 1 { y_j } else { x_j };
                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: None,
                    sparsity: None
                }
            },
            LMul => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in lmul");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                let (y_i, y_j) = expr_schema(&expr, 1).get_mat();
                dims_ok(*x_i, *x_j, *y_i, *y_j);
                let row = if *x_i == 1 { y_i } else { x_i };
                let col = if *x_j == 1 { y_j } else { x_j };
                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: None,
                    sparsity: None
                }
            },
            MMul => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in mmul");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                let (y_i, y_j) = expr_schema(&expr, 1).get_mat();
                debug_assert_eq!(*x_j, *y_i, "wrong dimensions in mmul");
                Meta {
                    schema: Some(Schema::Mat(*x_i, *y_j)),
                    nnz: None,
                    sparsity: None
                }
            },
            LTrs => {
                debug_assert_eq!(expr.children.len(), 1, "wrong length in transpose");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                Meta {
                    schema: Some(Schema::Mat(*x_j , *x_i)),
                    nnz: None,
                    sparsity: None
                }
            },
            Srow => {
                debug_assert_eq!(expr.children.len(), 1, "wrong length in transpose");
                let x_i = expr_schema(&expr, 0).get_mat().0;
                Meta {
                    schema: Some(Schema::Mat(*x_i , 1)),
                    nnz: None,
                    sparsity: None
                }
            },
            Scol => {
                debug_assert_eq!(expr.children.len(), 1, "wrong length in transpose");
                let x_j = expr_schema(&expr, 0).get_mat().1;
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
                debug_assert_eq!(expr.children.len(), 3, "wrong length in lmat");
                let i = expr_schema(&expr, 0).get_name();
                let j = expr_schema(&expr, 1).get_name();
                let (x_row, x_col) = expr_schema(&expr, 2).get_mat();
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
                debug_assert_eq!(expr.children.len(), 3, "wrong length in ubind");
                let i = expr_schema(&expr, 0).get_name();
                let j = expr_schema(&expr, 1).get_name();
                let x = expr_schema(&expr, 2).get_schm();
                let row = *x.get(i).unwrap_or(&1);
                let col = *x.get(j).unwrap_or(&1);
                Meta {
                    schema: Some(Schema::Mat(row, col)),
                    nnz: None,
                    sparsity: None
                }
            },
            LLit => {
                debug_assert_eq!(expr.children.len(), 1, "wrong length in lmat");
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

fn expr_schema<'a>(expr: &Expr<Math, &'a Meta>, i: usize) -> &'a Schema {
    expr.children[i].schema.as_ref().unwrap()
}

fn dims_ok(x_i: usize, x_j: usize, y_i: usize, y_j: usize) {
    debug_assert!(
        (x_i == y_i && x_j == y_j)
            || (x_i == y_i && y_i == 1)
            || (x_i == y_i && x_i == 1)
            || (x_i == 1 && x_j == y_j)
            || (y_i == 1 && x_j == y_j)
            || (x_i == 1 && x_j == 1)
            || (y_i == 1 && y_j == 1),
        format!("{:?}", (x_i, x_j, y_i, y_j))
    );
}

define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub enum Math {
        // LA
        LMat = "lmat", LAdd = "l+", LMin = "l-",
        LMul = "l*", MMul = "m*", LTrs = "trans",
        Srow = "srow", Scol = "scol", Sall = "sall",
        Bind = "b+", Ubnd = "b-", LLit = "llit",
        // RA
        Add = "+", Mul = "*", Agg = "sum",
        Lit = "lit", Var = "var", Mat = "mat",
        Dim = "dim", Nnz = "nnz", Sub = "subst",
        Num(Number), Str(String),
    }
}

impl Language for Math {
    fn cost(&self, children: &[u64]) -> u64 {
        use Math::*;
        println!("{:?}", self);
        let cost = match self {
            LMat | LAdd | LMin | LMul |
            MMul | LTrs | Srow | Scol |
            Sall | LLit |
            Num(_) | Str(_)=> 1,
            _ => 100
        };
        cost + children.iter().sum::<u64>()
    }
}
