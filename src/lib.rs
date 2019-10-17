use egg::{
    define_term,
    egraph::{AddResult, EClass},
    expr::{Expr, Language, QuestionMarkName, Id, RecExpr},
    //extract::{calculate_cost, Extractor},
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
                Meta::Attr(s.clone())
            },
            Math::Num(n) => {
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
    let rw = |name, l, r| Math::parse_rewrite::<Meta>(name, l, r).unwrap();
    vec![
        rw("+-commutative", "(+ ?a ?b)", "(+ ?b ?a)"),
        rw("*-commutative", "(* ?a ?b)", "(* ?b ?a)"),

        rw("associate-+r+", "(+ ?a (+ ?b ?c))", "(+ (+ ?a ?b) ?c)"),
        rw("associate-+l+", "(+ (+ ?a ?b) ?c)", "(+ ?a (+ ?b ?c))"),
        rw("associate-+r-", "(+ ?a (- ?b ?c))", "(- (+ ?a ?b) ?c)"),
        rw("associate-+l-", "(+ (- ?a ?b) ?c)", "(- ?a (- ?b ?c))"),
        rw("associate--r+", "(- ?a (+ ?b ?c))", "(- (- ?a ?b) ?c)"),
        rw("associate--l+", "(- (+ ?a ?b) ?c)", "(+ ?a (- ?b ?c))"),
        rw("associate--l-", "(- (- ?a ?b) ?c)", "(- ?a (+ ?b ?c))"),
        rw("associate--r-", "(- ?a (- ?b ?c))", "(+ (- ?a ?b) ?c)"),
        rw("associate-*r*", "(* ?a (* ?b ?c))", "(* (* ?a ?b) ?c)"),
        rw("associate-*l*", "(* (* ?a ?b) ?c)", "(* ?a (* ?b ?c))"),
        rw("associate-*r/", "(* ?a (/ ?b ?c))", "(/ (* ?a ?b) ?c)"),
        rw("associate-*l/", "(* (/ ?a ?b) ?c)", "(/ (* ?a ?c) ?b)"),
        rw("associate-/r*", "(/ ?a (* ?b ?c))", "(/ (/ ?a ?b) ?c)"),
        rw("associate-/l*", "(/ (* ?b ?c) ?a)", "(/ ?b (/ ?a ?c))"),
        rw("associate-/r/", "(/ ?a (/ ?b ?c))", "(* (/ ?a ?b) ?c)"),
        rw("associate-/l/", "(/ (/ ?b ?c) ?a)", "(/ ?b (* ?a ?c))"),

        rw("subst-+",      "(subst ?e ?v (+ ?a ?b))",     "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw("subst-*",      "(subst ?e ?v (* ?a ?b))",     "(* (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw("subst-matrix", "(subst ?e ?v (mat ?a ?i ?j))", "(mat ?a (subst ?e ?v ?i) (subst ?e ?v ?j))"),
        rw("subst-lit",    "(subst ?e ?v (lit ?n))",      "(lit ?n)"),

        rw("matrix-swap-dims", "(mat ?x ?i ?j)", "(mat ?x ?j ?i)"),

        rw("distribute-lft-in",    "(* ?a (+ ?b ?c))",        "(+ (* ?a ?b) (* ?a ?c))"),
        rw("distribute-rgt-in",    "(* ?a (+ ?b ?c))",        "(+ (* ?b ?a) (* ?c ?a))"),
        rw("distribute-lft-out",   "(+ (* ?a ?b) (* ?a ?c))", "(* ?a (+ ?b ?c))"),
        rw("distribute-lft-out--", "(- (* ?a ?b) (* ?a ?c))", "(* ?a (- ?b ?c))"),
        rw("distribute-rgt-out",   "(+ (* ?b ?a) (* ?c ?a))", "(* ?a (+ ?b ?c))"),
        rw("distribute-rgt-out--", "(- (* ?b ?a) (* ?c ?a))", "(* ?a (- ?b ?c))"),
        rw("distribute-lft1-in",   "(+ (* ?b ?a) ?a)",        "(* (+ ?b 1) ?a)"),
        rw("distribute-rgt1-in",   "(+ ?a (* ?c ?a))",        "(* (+ ?c 1) ?a)"),

        rw("pullup-add",    "(sum ?i (+ ?a ?b))",            "(+ (sum ?i ?a) (sum ?i ?b))"),
        rw("pushdown-add",  "(+ (sum ?i ?a) (sum ?i ?b))",  "(sum ?i (+ ?a ?b))",),

        rw("swap-agg", "(sum ?i (sum ?j ?a))", "(sum ?j (sum ?i ?a))"),

        Rewrite::new(
            "foundit",
            Math::parse_pattern(
                "(+ (sum ?i (sum ?j (+ (* (mat ?x ?i ?j) (mat ?x ?i ?j)) (+ \
                 (* (mat ?x ?i ?j) (sum ?k (* (mat ?u ?i ?k) (mat ?v ?k ?j)))) \
                 (* (mat ?x ?i ?j) (sum ?k (* (mat ?u ?i ?k) (mat ?v ?k ?j)))))))) \
                 (sum ?c (sum ?a (* \
                 (sum ?b (* (mat ?u ?a ?b) (mat ?u ?b ?c)))\
                 (sum ?d (* (mat ?v ?a ?d) (mat ?v ?d ?c)))))))",).unwrap(),
            Foundit,
        ),

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
            "pushdown_mul",
            Math::parse_pattern("(* ?a (sum ?i ?b))").unwrap(),
            PushMul {
                a: "?a".parse().unwrap(),
                i: "?i".parse().unwrap(),
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
struct Foundit;

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
struct PushMul {
    i: QuestionMarkName,
    a: QuestionMarkName,
    b: QuestionMarkName,
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

impl Applier<Math, Meta> for Foundit {
    fn apply(&self, _egraph: &mut EGraph, _map: &WildMap) -> Vec<AddResult> {
        panic!("FOUNDITTT")
    }
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

impl Applier<Math, Meta> for PushMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&self.a][0];
        let i = map[&self.i][0];
        let b = map[&self.b][0];

        let ((i_i, i_n), a_schema) = if let (Meta::Dims(i, n) , Meta::Schema(a_s))
            = (egraph[i].metadata.clone(), egraph[a].metadata.clone()) {
                ((i, n), a_s)
            } else {
                panic!("wrong schema in push multiply");
            };

        let mut res = Vec::new();

        if !a_schema.contains_key(&i_i) {
            let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, b]));
            let agg = egraph.add(Expr::new(Math::Agg, smallvec![i, mul.id]));
            res.push(agg);
        } else {
            let mut s = DefaultHasher::new();
            [i, a, b].hash(&mut s);
            let fresh_s = "v".to_owned() + &(s.finish() % 976521).to_string();

            let fresh_v = egraph.add(Expr::new(Math::Var(fresh_s), smallvec![]));
            let fresh_n = egraph.add(Expr::new(Math::Num(i_n as i32), smallvec![]));
            let fresh_dim = egraph.add(Expr::new(Math::Dim, smallvec![fresh_v.id, fresh_n.id]));

            let b_subst = egraph.add(Expr::new(Math::Subst, smallvec![fresh_dim.id, i, b]));
            let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, b_subst.id]));
            let agg = egraph.add(Expr::new(Math::Agg, smallvec![fresh_dim.id, mul.id]));
            res.push(agg);
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

pub fn extract(egraph: EGraph, root: Id) {
    // generate variables
    // Br = variable for root
    // Bn = variable for each node
    // Bq = variable for each class

    // generate constraints
    // Br: must pick root
    // Fn: Bn => AND Bq in n.children

    let mut problem = LpProblem::new("wormhole", LpObjective::Minimize);

    let br = "bq".to_owned() + &root.to_string();

    //let mut constraint_fn = HashMap::new();
    // TODO might need to iterate over eclass for this
    // to work properly
    let var_bns: BiMap<_,_> = egraph.memo.keys().map(|e| {
        let mut s = DefaultHasher::new();
        e.hash(&mut s);
        let bnv = "bn".to_owned() + &s.finish().to_string();
        let bn = LpBinary::new(&bnv);
        (e, SymVar(bn))
    }).collect();

    let var_bqs: BiMap<_,_> = egraph.classes().map(|c| {
        let bqv = "bq".to_owned() + &c.id.to_string();
        let bq = LpBinary::new(&bqv);
        (c.id, SymVar(bq))
    }).collect();

    // map each Bn to vec of Bq
    // Gq: Bq => OR Bn in q.nodes

    //let mut constraint_gq = HashMap::new();

    // map each Bq to vec of Bn

    // generate objective
    // min SUM_n Bn * Cn
    // map each Bn to cost

    // 2 maps: map Bn to Bqs, and map Bq to Bns

    let obj_vec: Vec<LpExpression> = {
        var_bns.iter().map(|(_e, bin)| {
            let coef = 2;
            coef * &bin.0
        }).collect()
    };

    problem += obj_vec.sum();

    // Br: must pick root
    problem += (0 + &var_bqs.get_by_left(&root).unwrap().0).equal(1);

    for node in egraph.memo.keys() {
        // Fn: Bn => AND Bq in n.children
        // (not Bn) or (AND Bq)
        for class in node.children.iter() {
            // (1-Bn) + bq > 0
            problem += ((1-&var_bns.get_by_left(&node).unwrap().0) + &var_bqs.get_by_left(class).unwrap().0).ge(1);
        }
    }

    for class in egraph.classes() {
        // Gq: Bq => OR Bn in q.nodes
        // (not Bq) or (OR Bn)
        // (1-Bq) + (sum Bn) > 0
        problem += ((1-&var_bqs.get_by_left(&class.id).unwrap().0) + sum(&class.nodes, |n| &var_bns.get_by_left(&n).unwrap().0)).ge(1);
    }

    let solver = GurobiSolver::new();
    let result = solver.run(&problem);

    assert!(result.is_ok(), result.unwrap_err());

    let (solver_status, var_values) = result.unwrap();

    let mut selected = HashSet::new();

    for (var_name, var_value) in &var_values {
        let int_var_value = *var_value as u32;
        if int_var_value == 1{
            if let Some(&v) = var_bns.get_by_right(&SymVar(LpBinary::new(var_name))) {
                //println!("{}", v.op);
                selected.insert(v);
            }
        }
    }

    let best = best_expr(&egraph, root, &selected);
    println!("{}", best.pretty(40));
}

fn best_expr(egraph: &EGraph, class: Id, selected: &HashSet<&Expr<Math, Id>>) -> RecExpr<Math> {
    let eclass = egraph.find(class);
    let best_node = egraph[eclass]
        .iter()
        .find(|n| selected.contains(n))
        .expect("no node selected in class");

    best_node
        .clone()
        .map_children(|child| best_expr(egraph, child, selected))
        .into()
}

#[derive(PartialEq)]
struct SymVar(LpBinary);

impl Eq for SymVar {}

impl Hash for SymVar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.name.hash(state);
    }
}
