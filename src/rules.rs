use crate::{Math, Meta, EGraph, Schema};

use egg::{
    egraph::{AddResult},
    //expr::{Expr, Language, QuestionMarkName, Id, RecExpr},
    expr::{Expr, QuestionMarkName},
    //extract::{calculate_cost, Extractor},
    parse::ParsableLanguage,
    pattern::{Applier, Rewrite, WildMap},
};

use smallvec::smallvec;
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite<Math, Meta>> {
    let rw = |name, l, r| Math::parse_rewrite::<Meta>(name, l, r).unwrap();
    vec![
        rw("+-commutative", "(+ ?a ?b)", "(+ ?b ?a)"),
        rw("*-commutative", "(* ?a ?b)", "(* ?b ?a)"),

        rw("associate-+r+", "(+ ?a (+ ?b ?c))", "(+ (+ ?a ?b) ?c)"),
        rw("associate-+l+", "(+ (+ ?a ?b) ?c)", "(+ ?a (+ ?b ?c))"),
        rw("associate-*r*", "(* ?a (* ?b ?c))", "(* (* ?a ?b) ?c)"),
        rw("associate-*l*", "(* (* ?a ?b) ?c)", "(* ?a (* ?b ?c))"),

        rw("subst-+",      "(subst ?e ?v (+ ?a ?b))",     "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw("subst-*",      "(subst ?e ?v (* ?a ?b))",     "(* (subst ?e ?v ?a) (subst ?e ?v ?b))"),

        rw("add-2-mul", "(+ ?x ?x)", "(* (lit 2) ?x)"),

        rw("subst-matrix", "(subst ?e ?v (mat ?a ?i ?j ?z))", "(mat ?a (subst ?e ?v ?i) (subst ?e ?v ?j) ?z)"),
        rw("subst-lit",    "(subst ?e ?v (lit ?n))",      "(lit ?n)"),
        rw("subst-var",    "(subst ?e ?v (var ?n))",      "(var ?n)"),

        rw("matrix-swap-dims", "(mat ?x ?i ?j ?z)", "(mat ?x ?j ?i ?z)"),

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

        //Rewrite::new(
        //    "foundit",
        //    Math::parse_pattern(
        //        "(+ (sum ?i (sum ?j (+ (* (mat ?x ?i ?j ?za) (mat ?x ?i ?j ?zb)) (+ \
        //         (* (mat ?x ?i ?j ?zc) (sum ?k (* (mat ?u ?i ?k ?zd) (mat ?v ?k ?j ?ze)))) \
        //         (* (mat ?x ?i ?j ?zf) (sum ?k (* (mat ?u ?i ?k ?zg) (mat ?v ?k ?j ?zh)))))))) \
        //         (sum ?c (sum ?a (* \
        //         (sum ?b (* (mat ?u ?a ?b ?zi) (mat ?u ?b ?c ?zj)))\
        //         (sum ?d (* (mat ?v ?a ?d ?zk) (mat ?v ?d ?c ?zl)))))))",).unwrap(),
        //    Foundit,
        //),

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
            let sub_body = egraph.add(Expr::new(Math::Sub, smallvec![e, v1, body]));
            egraph.add(Expr::new(Math::Agg, smallvec![v2, sub_body.id]))
        };

        vec![res]
    }
}

impl Applier<Math, Meta> for SumIA {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let i = map[&self.i][0];
        let a = map[&self.a][0];

        let i_m = egraph[i].metadata.clone();
        let a_m = egraph[a].metadata.clone();

        let mut res = Vec::new();

        if let (Schema::Dims(k, n), Schema::Schm(body)) =
            (&i_m.schema.unwrap(), &a_m.schema.unwrap()) {
            if !body.contains_key(k) {
                let i_abs = egraph.add(Expr::new(Math::Num(*n as i32), smallvec![]));
                let i_val = egraph.add(Expr::new(Math::Lit, smallvec![i_abs.id]));
                let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, i_val.id]));
                res.push(mul);
            }
        } else {
            panic!("wrong schema in aggregate");
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

        if let (Schema::Dims(k, n), Schema::Schm(body)) =
            (&i_schema.schema.unwrap(), &a_schema.schema.unwrap()) {
            if !body.contains_key(k) {
                let agg = egraph.add(Expr::new(Math::Agg, smallvec![i, b]));
                let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, agg.id]));
                res.push(mul);
            }
        } else {
            panic!("wrong schema in aggregate");
        }

        res
    }
}

impl Applier<Math, Meta> for PushMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&self.a][0];
        let i = map[&self.i][0];
        let b = map[&self.b][0];

        let ((i_i, i_n), a_schema) = if let (Schema::Dims(i, n) , Schema::Schm(a_s))
            = (egraph[i].metadata.clone().schema.unwrap(),
               egraph[a].metadata.clone().schema.unwrap()) {
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

            let fresh_v = egraph.add(Expr::new(Math::Str(fresh_s), smallvec![]));
            let fresh_n = egraph.add(Expr::new(Math::Num(i_n as i32), smallvec![]));
            let fresh_dim = egraph.add(Expr::new(Math::Dim, smallvec![fresh_v.id, fresh_n.id]));

            let b_subst = egraph.add(Expr::new(Math::Sub, smallvec![fresh_dim.id, i, b]));
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
