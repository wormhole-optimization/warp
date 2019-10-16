use egg::{
    define_term,
    egraph::{AddResult, EClass},
    expr::{Expr, Language, QuestionMarkName},
    //extract::{calculate_cost, Extractor},
    parse::ParsableLanguage,
    pattern::{Applier, Rewrite, WildMap},
};

///use log::*;
use smallvec::smallvec;
use std::collections::HashMap;
use std::i32;

pub type EGraph = egg::egraph::EGraph<Math, Meta>;

type Number = i32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Meta {
    Schema(HashMap<String, usize>),
    Dims(String, usize),
    Attr(String),
    Size(usize),
}

impl Meta {
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
        if let (Meta::Schema(l), Meta::Schema(r)) = (self, other) {
            assert_eq!(l, r, "merging expressions with different schema");
        }
        // TODO check which way schema is merged
        println!("new schema {:?}", self);
        self.clone()
    }

    fn make(expr: Expr<Math, &Self>) -> Self {
        let schema = match expr.op {
            Math::Add => {
                assert_eq!(expr.children.len(), 2, "wrong length in add");
                let x_schema = &expr.children[0];
                let y_schema = &expr.children[1];
                x_schema.union(y_schema)
            },
            Math::Mul => {
                assert_eq!(expr.children.len(), 2, "wrong length in mul");
                let x_schema = &expr.children[0];
                let y_schema = &expr.children[1];
                x_schema.union(y_schema)
            },
            Math::Agg => {
                assert_eq!(expr.children.len(), 2, "wrong length in sum");
                let dim = &expr.children[0];
                let body = &expr.children[1];

                let (k, mut body_schema) =
                    if let (Meta::Dims(i, n), Meta::Schema(schema)) = (dim, body) {
                        (i, schema.clone())
                    } else {
                        panic!("wrong schema in aggregate")
                    };

                body_schema.remove(k);
                Meta::Schema(body_schema)
            },
            Math::Lit => {
                Meta::Schema(HashMap::default())
            },
            Math::Matrix => {
                assert_eq!(expr.children.len(), 3, "wrong length in matrix");
                let i_schema = &expr.children[1];
                let j_schema = &expr.children[2];
                if let (Meta::Dims(i, n), Meta::Dims(j, m)) = (i_schema, j_schema) {
                    let res: HashMap<_,_> = vec![(i.clone(), *n), (j.clone(), *m)]
                        .into_iter().collect();
                    Meta::Schema(res)
                } else {
                    panic!("wrong schema in matrix")
                }
            },
            Math::Dim => {
                assert_eq!(expr.children.len(), 2, "wrong length in dim");
                let i_schema = &expr.children[0];
                let n_schema = &expr.children[1];
                if let (Meta::Attr(i), Meta::Size(n)) = (i_schema, n_schema) {
                    Meta::Dims(i.clone(), *n)
                } else {
                    panic!("wrong schema in dim {:?}", (i_schema, n_schema))
                }
            },
            Math::Subst => {
                assert_eq!(expr.children.len(), 3, "wrong length in subst");
                let e_schema = &expr.children[0];
                let v_schema = &expr.children[1];
                let body_schema = &expr.children[2];

                let (e_i, e_n) = if let Meta::Dims(i, n) = e_schema {
                    (i, n)
                } else {
                    panic!("wrong schema in subst e")
                };

                let (v_i, v_n) = if let Meta::Dims(i, n) = v_schema {
                    (i, n)
                } else {
                    panic!("wrong schema in subst v")
                };

                match body_schema {
                    Meta::Schema(schema) => {
                        let mut res = schema.clone();
                        if let Some(m) = res.remove(v_i) {
                            res.insert(e_i.clone(), m);
                        }
                        Meta::Schema(res)
                    },
                    Meta::Dims(body_i, body_n) => {
                        if body_i == v_i {
                            Meta::Dims(e_i.clone(), *e_n)
                        } else {
                            Meta::Dims(body_i.clone(), *body_n)
                        }
                    },
                    _ => panic!("cannot subst for attr. and size")
                }
            },
            Math::Var(s) => {
                println!("var schema{:?}", s);
                Meta::Attr(s.clone())
            },
            Math::Num(n) => {
                println!("num schema{:?}", n);
                Meta::Size(n as usize)
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
#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite<Math, Meta>> {
    let _rw = |name, l, r| Math::parse_rewrite::<Meta>(name, l, r).unwrap();
    vec![
        Rewrite::new(
            "agg-subst",
            Math::parse_pattern("(subst ?e ?v1 (sum ?v2 ?body))",).unwrap(),
            SubstAgg {
                e: "?e".parse().unwrap(),
                v1: "?v1".parse().unwrap(),
                v2: "?v2".parse().unwrap(),
                body: "?body".parse().unwrap(),
            },
        ),
        Rewrite::new(
            "sum_i_a",
            Math::parse_pattern("(sum ?i ?a)").unwrap(),
            SumIA {
                i: "?i".parse().unwrap(),
                a: "?a".parse().unwrap(),
            },
        ),
        Rewrite::new(
            "pullup_mul",
            Math::parse_pattern("(sum ?i (* ?a ?b))").unwrap(),
            PullMul {
                i: "?i".parse().unwrap(),
                a: "?a".parse().unwrap(),
                b: "?b".parse().unwrap(),
            }
        ),
        Rewrite::new(
            "dim_subst",
            Math::parse_pattern("(subst ?e (dim ?v ?m) (dim ?i ?n))").unwrap(),
            DimSubst {
                e: "?e".parse().unwrap(),
                v: "?v".parse().unwrap(),
                i: "?i".parse().unwrap(),
                n: "?n".parse().unwrap(),
            }
        ),

    ]
}

#[derive(Debug)]
struct SubstAgg {
    e: QuestionMarkName,
    v1: QuestionMarkName,
    v2: QuestionMarkName,
    body: QuestionMarkName,
}

#[derive(Debug)]
struct SumIA {
    i: QuestionMarkName,
    a: QuestionMarkName,
}

#[derive(Debug)]
struct PullMul {
    i: QuestionMarkName,
    a: QuestionMarkName,
    b: QuestionMarkName,
}

#[derive(Debug)]
struct DimSubst {
    e: QuestionMarkName,
    v: QuestionMarkName,
    i: QuestionMarkName,
    n: QuestionMarkName,
}

impl Applier<Math, Meta> for SubstAgg {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let v1 = map[&self.v1][0];
        let v2 = map[&self.v2][0];
        let e = map[&self.e][0];
        let body = map[&self.body][0];

        let res = if v1 == v2 {
            egraph.add(Expr::new(Math::Agg, smallvec![v2, body]))
        } else {
            let sub_body = egraph.add(Expr::new(Math::Subst, smallvec![e, v1, body]));
            egraph.add(Expr::new(Math::Agg, smallvec![v2, sub_body.id]))
        };

        vec![res]
    }
}

impl Applier<Math, Meta> for SumIA {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let i = map[&self.i][0];
        let a = map[&self.a][0];

        let i_schema = egraph[i].metadata.clone();
        let a_schema = egraph[a].metadata.clone();

        let mut res = Vec::new();

        if let (Meta::Dims(k, n), Meta::Schema(body)) = (&i_schema, &a_schema) {
            if !body.contains_key(k) {
                let i_abs = egraph.add(Expr::new(Math::Num(*n as i32), smallvec![]));
                let i_val = egraph.add(Expr::new(Math::Lit, smallvec![i_abs.id]));
                let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, i_val.id]));
                res.push(mul);
            }
        } else {
            panic!("wrong schema in aggregate i:{:?} body:{:?}", i_schema, a_schema);
        }

        res
    }
}


impl Applier<Math, Meta> for PullMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let i = map[&self.i][0];
        let a = map[&self.a][0];
        let b = map[&self.b][0];

        let i_schema = egraph[i].metadata.clone();
        let a_schema = egraph[a].metadata.clone();

        let mut res = Vec::new();

        if let (Meta::Dims(k, n), Meta::Schema(body)) = (&i_schema, &a_schema) {
            if !body.contains_key(k) {
                let agg = egraph.add(Expr::new(Math::Agg, smallvec![i, b]));
                let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, agg.id]));
                res.push(mul);
            }
        } else {
            panic!("wrong schema in aggregate i:{:?} body:{:?}", i_schema, a_schema);
        }

        res
    }
}

impl Applier<Math, Meta> for DimSubst {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let e = map[&self.e][0];
        let v = map[&self.v][0];
        let i = map[&self.i][0];
        let n = map[&self.n][0];

        let res = if i == v {
            AddResult {
                was_there: true,
                id: e
            }
        } else {
            egraph.add(Expr::new(Math::Dim, smallvec![i, n]))
        };

        vec![res]
    }
}
