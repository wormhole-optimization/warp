use egg::{
    define_term,
    egraph::{AddResult, EClass},
    expr::{Expr, Language, QuestionMarkName, Id, RecExpr},
    parse::ParsableLanguage,
    pattern::{Applier, Rewrite, WildMap},
};



///use log::*;
use smallvec::smallvec;
use std::collections::{HashMap, HashSet};
use std::i32;
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

use lp_modeler::solvers::{GurobiSolver, SolverTrait};
use lp_modeler::dsl::*;
use lp_modeler::format::lp_format::LpFileFormat;

use bimap::BiMap;
use ordered_float::NotNan;

mod rules;
pub use rules::rules;

mod extract;
pub use extract::*;

pub type EGraph = egg::egraph::EGraph<Math, Meta>;

type Number = i32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    schema: Schema,
    sparsity: Sparsity,
    nnz: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Sparsity {
    NA,
    One,
    Zero,
    Sparse(NotNan<f64>)
}

impl Sparsity {
    fn merge(&self, other: &Sparsity, op: Math) -> Self {
        match op {
            Math::Add => match self {
                Self::NA => Self::Sparse(NotNan::from(0 as f64)),
                Self::One => Self::Sparse(NotNan::from(0 as f64)),
                Self::Zero => other.clone(),
                Self::Sparse(s1) => match other {
                    Self::NA => Self::Sparse(NotNan::from(0 as f64)),
                    Self::One => Self::Sparse(NotNan::from(0 as f64)),
                    Self::Zero => Self::Sparse(*s1),
                    Self::Sparse(s2) => Self::Sparse(std::cmp::min(
                        NotNan::from(1 as f64), *s1 + *s2)),
                }
            },
            Math::Mul => match self {
                Self::NA => other.clone(),
                Self::One => other.clone(),
                Self::Zero => Self::Sparse(NotNan::from(1 as f64)),
                Self::Sparse(s1) => match other {
                    Self::NA => Self::Sparse(*s1),
                    Self::One => Self::Sparse(*s1),
                    Self::Zero => Self::Sparse(NotNan::from(1 as f64)),
                    Self::Sparse(s2) => Self::Sparse(std::cmp::min(*s1, *s2)),
                }
            },
            _ => panic!("merging non sum/product")
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Schema {
    Schema(HashMap<String, usize>),
    Dims(String, usize),
    Attr(String),
    Size(usize),
}

impl Schema {
    fn union(&self, other: &Self) -> Self {
        if let (Self::Schema(s1), Self::Schema(s2)) = (self, other) {
            let mut res = s1.clone();
            res.extend(s2.clone());
            Self::Schema(res)
        } else {
            panic!("Unioning a non-schema")
        }
    }
}

impl egg::egraph::Metadata<Math> for Meta {
    type Error = std::convert::Infallible;
    fn modify(_eclass: &mut EClass<Math, Self>) {}
    fn merge(&self, other: &Self) -> Self {

        // merge sparsity and nnz
        let sparsity = match &self.sparsity {
            Sparsity::Sparse(s1) => {
                match &other.sparsity {
                    Sparsity::Sparse(s2) => Sparsity::Sparse(std::cmp::max(*s1, *s2)),
                    _other => self.sparsity.clone()
                }
            }
            other => other.clone(),
        };
        let nnz = std::cmp::min(self.nnz, other.nnz);

        // merge schema
        if let (Schema::Schema(l), Schema::Schema(r)) = (&self.schema, &other.schema) {
            assert_eq!(l, r, "merging expressions with different schema");
        }
        // TODO check which way schema is merged
        Meta {schema: self.schema.clone(), sparsity: sparsity, nnz: nnz}
    }

    fn make(expr: Expr<Math, &Self>) -> Self {
        let schema = match expr.op {
            Math::Add => {
                assert_eq!(expr.children.len(), 2, "wrong length in add");
                let x = &expr.children[0];
                let y = &expr.children[1];
                let schema = x.schema.union(&y.schema);

                let sparsity = x.sparsity.merge(&y.sparsity, Math::Add);

                let nnz = if let Schema::Schema(s1) = &schema {
                    let vol: usize = s1.values().product();
                    match sparsity {
                        Sparsity::Sparse(s2) => {
                            NotNan::from(vol as f64) * (NotNan::from(1 as f64)-s2)
                        },
                        _ => NotNan::from(0 as f64)
                    }
                } else {
                    panic!("wrong schema in add")
                };

                Meta {schema, sparsity, nnz: nnz.round() as usize }
            },
            Math::Mul => {
                assert_eq!(expr.children.len(), 2, "wrong length in mul");
                let x = &expr.children[0];
                let y = &expr.children[1];
                let schema = x.schema.union(&y.schema);

                let sparsity = x.sparsity.merge(&y.sparsity, Math::Mul);

                let nnz = if let Schema::Schema(s1) = &schema {
                    let vol: usize = s1.values().product();
                    match sparsity {
                        Sparsity::Sparse(s2) => {
                            NotNan::from(vol as f64) * (NotNan::from(1 as f64)-s2)
                        },
                        _ => NotNan::from(0 as f64)
                    }
                } else {
                    panic!("wrong schema in mul")
                };
                Meta {schema, sparsity, nnz: nnz.round() as usize }
            },
            Math::Agg => {
                assert_eq!(expr.children.len(), 2, "wrong length in sum");
                let dim = &expr.children[0];
                let body = &expr.children[1];

                let (k, mut body_schema) =
                    if let (Schema::Dims(i,n), Schema::Schema(schema)) =
                    (&dim.schema, &body.schema) {
                        (i, schema.clone())
                    } else {
                        panic!("wrong schema in aggregate")
                    };

                body_schema.remove(k);
                let schema = Schema::Schema(body_schema);
                let sparsity = if let Schema::Schema(s) = &schema {
                    let vol: usize = s.values().product();
                    Sparsity::Sparse(
                        std::cmp::min(
                            NotNan::from(1 as f64),
                            NotNan::from(body.nnz as f64) / NotNan::from(vol as f64)
                        )
                    )
                } else {
                    panic!("wrong schema in aggregate")
                };

                Meta {schema, sparsity, nnz: body.nnz}
            },
            Math::Lit => {
                let num = &expr.children[0];
                Meta {
                    schema: Schema::Schema(HashMap::default()),
                    sparsity: num.sparsity.clone(),
                    nnz: num.nnz
                }
            },
            Math::Matrix => {
                assert_eq!(expr.children.len(), 4, "wrong length in matrix");
                let i_schema = &expr.children[1];
                let j_schema = &expr.children[2];
                let nnz = &expr.children[3].nnz;

                let (schema, n, m) = if let (Schema::Dims(i, n), Schema::Dims(j, m)) = (&i_schema.schema, &j_schema.schema) {
                    let res: HashMap<_,_> = vec![(i.clone(), *n), (j.clone(), *m)]
                        .into_iter().collect();
                    (Schema::Schema(res), n, m)
                } else {
                    panic!("wrong schema in matrix")
                };

                Meta {
                    schema: schema,
                    nnz: *nnz,
                    sparsity: Sparsity::Sparse(NotNan::from(*nnz as f64 / (n * m) as f64))
                }
            },
            Math::Dim => {
                assert_eq!(expr.children.len(), 2, "wrong length in dim");
                let i = &expr.children[0];
                let n = &expr.children[1];
                let schema = if let (Schema::Attr(i), Schema::Size(n)) = (&i.schema, &n.schema) {
                    Schema::Dims(i.clone(), *n)
                } else {
                    panic!("wrong schema in dim {:?}", (i, n))
                };
                Meta {
                    schema: schema,
                    nnz: 0,
                    sparsity: Sparsity::Sparse(NotNan::from(1 as f64))
                }
            },
            Math::Subst => {
                assert_eq!(expr.children.len(), 3, "wrong length in subst");
                let e = &expr.children[0];
                let v = &expr.children[1];
                let body = &expr.children[2];

                let (e_i, e_n) = if let Schema::Dims(i, n) = &e.schema {
                    (i, n)
                } else {
                    panic!("wrong schema in subst e")
                };

                let (v_i, v_n) = if let Schema::Dims(i, n) = &v.schema {
                    (i, n)
                } else {
                    panic!("wrong schema in subst v")
                };

                let schema = match &body.schema {
                    Schema::Schema(schema) => {
                        let mut res = schema.clone();
                        if let Some(m) = res.remove(v_i) {
                            res.insert(e_i.clone(), m);
                        }
                        Schema::Schema(res)
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
                    schema: schema,
                    nnz: body.nnz,
                    sparsity: body.sparsity.clone()
                }
            },
            Math::Var(s) => {
                Meta {
                    schema: Schema::Attr(s.clone()),
                    nnz: 0,
                    sparsity: Sparsity::NA
                }
            },
            Math::Num(n) => {
                Meta {
                    schema: Schema::Size(n as usize),
                    nnz: n as usize,
                    sparsity: match n {
                        1 => Sparsity::One,
                        0 => Sparsity::Zero,
                        _ => Sparsity::NA
                    }
                }
            },
            Math::Nnz => {
                let nnz = &expr.children[0].nnz;
                Meta {
                    schema: Schema::Size(0),
                    nnz: *nnz,
                    sparsity: Sparsity::NA,
                }
            }
        };
        schema
    }

}

define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub enum Math {
        Add = "+",
        Mul = "*",
        Agg = "sum",
        Lit = "lit",

        Matrix = "mat",
        Dim = "dim",
        Nnz = "nnz",

        Subst = "subst",
        Num(Number),
        Var(String),
    }
}

impl Language for Math {
    fn cost(&self, children: &[u64]) -> u64 {
        let cost = 1;
        cost + children.iter().sum::<u64>()
    }
}
