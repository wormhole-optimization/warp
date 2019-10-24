use crate::{Math, Meta, EGraph, Schema};

use egg::{
    egraph::{AddResult},
    expr::{Expr, QuestionMarkName},
    parse::ParsableLanguage,
    pattern::{Applier, Rewrite, WildMap},
};

use smallvec::smallvec;
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

#[rustfmt::skip]
pub fn trans_rules() -> Vec<Rewrite<Math, Meta>> {
    let rw = |name, l, r| Math::parse_rewrite::<Meta>(name, l, r).unwrap();
    vec![
        rw("la-minus", "(l- ?a ?b)", "(l+ ?a (l* (lit -1) ?b))"),
        Rewrite::new(
            "la_mul",
            Math::parse_pattern("(l* ?x ?y)").unwrap(),
            LAMul {
                x: "?x".parse().unwrap(),
                y: "?y".parse().unwrap(),
            }
        ),
        Rewrite::new(
            "la_add",
            Math::parse_pattern("(l+ ?x ?y)").unwrap(),
            LAAdd {
                x: "?x".parse().unwrap(),
                y: "?y".parse().unwrap(),
            }
        ),
        Rewrite::new(
            "la_mmul",
            Math::parse_pattern("(m* ?x ?y)").unwrap(),
            LAMMul {
                x: "?x".parse().unwrap(),
                y: "?y".parse().unwrap(),
            }
        ),
        Rewrite::new(
            "la-trans",
            Math::parse_pattern("(trans ?a)").unwrap(),
            LATrans {
                a: "?a".parse().unwrap(),
            }
        ),
        Rewrite::new(
            "la-srow",
            Math::parse_pattern("(srow ?a)").unwrap(),
            LASrow {
                a: "?a".parse().unwrap(),
            }
        ),
        Rewrite::new(
            "la-scol",
            Math::parse_pattern("(scol ?a)").unwrap(),
            LAScol {
                a: "?a".parse().unwrap(),
            }
        ),
        Rewrite::new(
            "la-sall",
            Math::parse_pattern("(sall ?a)").unwrap(),
            LASall {
                a: "?a".parse().unwrap(),
            }
        ),
        Rewrite::new(
            "la-bind",
            Math::parse_pattern("(b+ ?k ?l (b- ?i ?j ?x))").unwrap(),
            LABind {
                i: "?i".parse().unwrap(),
                j: "?j".parse().unwrap(),
                k: "?k".parse().unwrap(),
                l: "?l".parse().unwrap(),
                x: "?x".parse().unwrap(),
            }
        ),
        rw("la-mat-bind", "(b+ ?k ?l (lmat ?x ?i ?j ?z))", "(mat ?x (dim ?k ?i) (dim ?l ?j) ?z)"),
        //Rewrite::new(
        //    "la-mat-bind",
        //    Math::parse_pattern("(b+ ?k ?l (lmat ?x ?i ?j ?z))").unwrap(),
        //    LAMatBind {
        //        i: "?i".parse().unwrap(),
        //        j: "?j".parse().unwrap(),
        //        k: "?k".parse().unwrap(),
        //        l: "?l".parse().unwrap(),
        //        x: "?x".parse().unwrap(),
        //        z: "?z".parse().unwrap(),
        //    }
        //),
        rw("la-lit-bind",  "(b+ ?i ?j (llit ?n))",            "(lit ?n)"),
        rw("subst-+",      "(subst ?e ?v (+ ?a ?b))",         "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw("subst-*",      "(subst ?e ?v (* ?a ?b))",         "(* (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw("subst-matrix", "(subst ?e ?v (mat ?a ?i ?j ?z))", "(mat ?a (subst ?e ?v ?i) (subst ?e ?v ?j) ?z)"),
        rw("subst-lit",    "(subst ?e ?v (lit ?n))",          "(lit ?n)"),
        rw("subst-var",    "(subst ?e ?v (var ?n))",          "(var ?n)"),
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
struct LAMatBind {
    i: QuestionMarkName,
    j: QuestionMarkName,
    k: QuestionMarkName,
    l: QuestionMarkName,
    x: QuestionMarkName,
    z: QuestionMarkName,
}

#[derive(Debug)]
struct LABind {
    i: QuestionMarkName,
    j: QuestionMarkName,
    k: QuestionMarkName,
    l: QuestionMarkName,
    x: QuestionMarkName,
}

#[derive(Debug)]
struct LASall {
    a: QuestionMarkName,
}

#[derive(Debug)]
struct LAScol {
    a: QuestionMarkName,
}

#[derive(Debug)]
struct LASrow {
    a: QuestionMarkName,
}

#[derive(Debug)]
struct LATrans {
    a: QuestionMarkName,
}

#[derive(Debug)]
struct LAMMul {
    x: QuestionMarkName,
    y: QuestionMarkName,
}

#[derive(Debug)]
struct LAAdd {
    x: QuestionMarkName,
    y: QuestionMarkName,
}

#[derive(Debug)]
struct LAMul {
    x: QuestionMarkName,
    y: QuestionMarkName,
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
struct LADimSubst {
    e: QuestionMarkName,
    v: QuestionMarkName,
    i: QuestionMarkName,
    n: QuestionMarkName,
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

        if e == v2 {
            panic!("substituting ahhhh")
        }
        // TODO what if e is v1
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

impl Applier<Math, Meta> for LADimSubst {
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

impl Applier<Math, Meta> for LAMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let x = map[&self.x][0];
        let y = map[&self.y][0];

        let x_schema = egraph[x].metadata.clone().schema.unwrap();
        let y_schema = egraph[y].metadata.clone().schema.unwrap();

        let (x_i, x_j, y_i, y_j) =
            if let (Schema::Mat(xrow, xcol), Schema::Mat(yrow, ycol))
            = (x_schema, y_schema) {
                (xrow, xcol, yrow, ycol)
            } else {
                panic!("wrong schema in lmul")
            };

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vmul_i".to_owned() + &fresh_s;
        let fresh_j = "vmul_j".to_owned() + &fresh_s;

        let bind_xi = if x_i == 1 {"_"} else { &fresh_i };
        let bind_xj = if x_j == 1 {"_"} else { &fresh_j };
        let bind_yi = if y_i == 1 {"_"} else { &fresh_i };
        let bind_yj = if y_j == 1 {"_"} else { &fresh_j };

        let ubnd_i = if x_i * y_i == 1 {"_"} else { &fresh_i };
        let ubnd_j = if x_j * y_j == 1 {"_"} else { &fresh_j };

        // [-i,j] (* [i,j]A [i,j]B)
        let a_i = egraph.add(Expr::new(Math::Str(bind_xi.to_owned()), smallvec![]));
        let a_j = egraph.add(Expr::new(Math::Str(bind_xj.to_owned()), smallvec![]));
        let b_i = egraph.add(Expr::new(Math::Str(bind_yi.to_owned()), smallvec![]));
        let b_j = egraph.add(Expr::new(Math::Str(bind_yj.to_owned()), smallvec![]));
        let u_i = egraph.add(Expr::new(Math::Str(ubnd_i.to_owned()), smallvec![]));
        let u_j = egraph.add(Expr::new(Math::Str(ubnd_j.to_owned()), smallvec![]));

        let a = egraph.add(Expr::new(Math::Bind, smallvec![a_i.id, a_j.id, x]));
        let b = egraph.add(Expr::new(Math::Bind, smallvec![b_i.id, b_j.id, y]));
        let mul = egraph.add(Expr::new(Math::Mul, smallvec![a.id, b.id]));
        let ubd = egraph.add(Expr::new(Math::Ubnd, smallvec![u_i.id, u_j.id, mul.id]));

        vec![ubd]
    }
}

impl Applier<Math, Meta> for LAAdd {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let x = map[&self.x][0];
        let y = map[&self.y][0];

        let x_schema = egraph[x].metadata.clone().schema.unwrap();
        let y_schema = egraph[y].metadata.clone().schema.unwrap();

        let (x_i, x_j, y_i, y_j) =
            if let (Schema::Mat(xrow, xcol), Schema::Mat(yrow, ycol))
            = (x_schema, y_schema) {
                (xrow, xcol, yrow, ycol)
            } else {
                panic!("wrong schema in ladd")
            };

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vadd_i".to_owned() + &fresh_s;
        let fresh_j = "vadd_j".to_owned() + &fresh_s;

        let bind_xi = if x_i == 1 {"_"} else { &fresh_i };
        let bind_xj = if x_j == 1 {"_"} else { &fresh_j };
        let bind_yi = if y_i == 1 {"_"} else { &fresh_i };
        let bind_yj = if y_j == 1 {"_"} else { &fresh_j };

        let ubnd_i = if x_i * y_i == 1 {"_"} else { &fresh_i };
        let ubnd_j = if x_j * y_j == 1 {"_"} else { &fresh_j };

        // [-i,j] (* [i,j]A [i,j]B)
        let a_i = egraph.add(Expr::new(Math::Str(bind_xi.to_owned()), smallvec![]));
        let a_j = egraph.add(Expr::new(Math::Str(bind_xj.to_owned()), smallvec![]));
        let b_i = egraph.add(Expr::new(Math::Str(bind_yi.to_owned()), smallvec![]));
        let b_j = egraph.add(Expr::new(Math::Str(bind_yj.to_owned()), smallvec![]));
        let u_i = egraph.add(Expr::new(Math::Str(ubnd_i.to_owned()), smallvec![]));
        let u_j = egraph.add(Expr::new(Math::Str(ubnd_j.to_owned()), smallvec![]));

        let a = egraph.add(Expr::new(Math::Bind, smallvec![a_i.id, a_j.id, x]));
        let b = egraph.add(Expr::new(Math::Bind, smallvec![b_i.id, b_j.id, y]));
        let add = egraph.add(Expr::new(Math::Add, smallvec![a.id, b.id]));
        let ubd = egraph.add(Expr::new(Math::Ubnd, smallvec![u_i.id, u_j.id, add.id]));

        vec![ubd]
    }
}

impl Applier<Math, Meta> for LAMMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let x = map[&self.x][0];
        let y = map[&self.y][0];

        let x_schema = egraph[x].metadata.clone().schema.unwrap();
        let y_schema = egraph[y].metadata.clone().schema.unwrap();

        let (x_i, x_j, y_j, y_k) =
            if let (Schema::Mat(xrow, xcol), Schema::Mat(yrow, ycol))
            = (x_schema, y_schema) {
                (xrow, xcol, yrow, ycol)
            } else {
                panic!("wrong schema in ladd")
            };

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vmmul_i".to_owned() + &fresh_s;
        let fresh_j = "vmmul_j".to_owned() + &fresh_s;
        let fresh_k = "vmmul_k".to_owned() + &fresh_s;

        let bind_xi = if x_i == 1 {"_"} else { &fresh_i };
        let bind_xj = if x_j == 1 {"_"} else { &fresh_j };
        let bind_yj = if y_j == 1 {"_"} else { &fresh_j };
        let bind_yk = if y_k == 1 {"_"} else { &fresh_k };

        let ubnd_i = if x_i == 1 {"_"} else { &fresh_i };
        let ubnd_k = if y_k == 1 {"_"} else { &fresh_k };

        let agg_j = if x_j * y_j == 1 {"_"} else {&fresh_j};

        // [-i,k] (sum j (* [i,j]A [j,k]B))
        let a_i = egraph.add(Expr::new(Math::Str(bind_xi.to_owned()), smallvec![]));
        let a_j = egraph.add(Expr::new(Math::Str(bind_xj.to_owned()), smallvec![]));
        let b_j = egraph.add(Expr::new(Math::Str(bind_yj.to_owned()), smallvec![]));
        let b_k = egraph.add(Expr::new(Math::Str(bind_yk.to_owned()), smallvec![]));

        let u_i = egraph.add(Expr::new(Math::Str(ubnd_i.to_owned()), smallvec![]));
        let u_k = egraph.add(Expr::new(Math::Str(ubnd_k.to_owned()), smallvec![]));

        let a = egraph.add(Expr::new(Math::Bind, smallvec![a_i.id, a_j.id, x]));
        let b = egraph.add(Expr::new(Math::Bind, smallvec![b_j.id, b_k.id, y]));
        let mul = egraph.add(Expr::new(Math::Mul, smallvec![a.id, b.id]));

        let res = if agg_j == "_" {
            egraph.add(Expr::new(Math::Ubnd, smallvec![u_i.id, u_k.id, mul.id]))
        } else {
            let j_dim = egraph.add(Expr::new(Math::Num(x_j as i32), smallvec![]));
            let agg_j_dim = egraph.add(Expr::new(Math::Dim, smallvec![a_j.id, j_dim.id]));
            let agg = egraph.add(Expr::new(Math::Agg, smallvec![agg_j_dim.id, mul.id]));
            egraph.add(Expr::new(Math::Ubnd, smallvec![u_i.id, u_k.id, agg.id]))
        };

        vec![res]
    }
}

impl Applier<Math, Meta> for LATrans {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&self.a][0];
        let a_schema = egraph[a].metadata.clone().schema.unwrap();

        let (a_i, a_j) =
            if let Schema::Mat(arow, acol)
            = a_schema {
                (arow, acol)
            } else {
                panic!("wrong schema in ladd")
            };

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vtrans_i".to_owned() + &fresh_s;
        let fresh_j = "vtrans_j".to_owned() + &fresh_s;

        let bind_ai = if a_i == 1 {"_"} else { &fresh_i };
        let bind_aj = if a_j == 1 {"_"} else { &fresh_j };

        // [-i,j] [j,i] A
        let a_i = egraph.add(Expr::new(Math::Str(bind_ai.to_owned()), smallvec![]));
        let a_j = egraph.add(Expr::new(Math::Str(bind_aj.to_owned()), smallvec![]));
        let a = egraph.add(Expr::new(Math::Bind, smallvec![a_i.id, a_j.id, a]));
        let ubd = egraph.add(Expr::new(Math::Ubnd, smallvec![a_j.id, a_i.id, a.id]));

        vec![ubd]
    }
}

impl Applier<Math, Meta> for LASrow {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&self.a][0];
        let a_schema = egraph[a].metadata.clone().schema.unwrap();

        let (a_i, a_j) =
            if let Schema::Mat(arow, acol)
            = a_schema {
                (arow, acol)
            } else {
                panic!("wrong schema in ladd")
            };

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsrow_i".to_owned() + &fresh_s;
        let fresh_j = "vsrow_j".to_owned() + &fresh_s;

        let bind_ai = if a_i == 1 {"_"} else { &fresh_i };
        let bind_aj = if a_j == 1 {"_"} else { &fresh_j };
        let bind_wild = "_";

        // [-i,_] (sum i [i,j] A)
        let ai = egraph.add(Expr::new(Math::Str(bind_ai.to_owned()), smallvec![]));
        let aj = egraph.add(Expr::new(Math::Str(bind_aj.to_owned()), smallvec![]));
        let wild = egraph.add(Expr::new(Math::Str(bind_wild.to_owned()), smallvec![]));
        let a = egraph.add(Expr::new(Math::Bind, smallvec![ai.id, aj.id, a]));

        let i_dim = egraph.add(Expr::new(Math::Num(a_i as i32), smallvec![]));
        let agg_i_dim = egraph.add(Expr::new(Math::Dim, smallvec![ai.id, i_dim.id]));
        let agg = egraph.add(Expr::new(Math::Agg, smallvec![agg_i_dim.id, a.id]));

        let ubd = egraph.add(Expr::new(Math::Ubnd, smallvec![ai.id, wild.id, agg.id]));

        vec![ubd]
    }
}

impl Applier<Math, Meta> for LAScol {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&self.a][0];
        let a_schema = egraph[a].metadata.clone().schema.unwrap();

        let (a_i, a_j) =
            if let Schema::Mat(arow, acol)
            = a_schema {
                (arow, acol)
            } else {
                panic!("wrong schema in ladd")
            };

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vscol_i".to_owned() + &fresh_s;
        let fresh_j = "vscol_j".to_owned() + &fresh_s;

        let bind_ai = if a_i == 1 {"_"} else { &fresh_i };
        let bind_aj = if a_j == 1 {"_"} else { &fresh_j };
        let bind_wild = "_";

        // [-_,j] (sum j [i,j] A)
        let ai = egraph.add(Expr::new(Math::Str(bind_ai.to_owned()), smallvec![]));
        let aj = egraph.add(Expr::new(Math::Str(bind_aj.to_owned()), smallvec![]));
        let wild = egraph.add(Expr::new(Math::Str(bind_wild.to_owned()), smallvec![]));
        let a = egraph.add(Expr::new(Math::Bind, smallvec![ai.id, aj.id, a]));

        let j_dim = egraph.add(Expr::new(Math::Num(a_j as i32), smallvec![]));
        let agg_j_dim = egraph.add(Expr::new(Math::Dim, smallvec![aj.id, j_dim.id]));
        let agg = egraph.add(Expr::new(Math::Agg, smallvec![agg_j_dim.id, a.id]));

        let ubd = egraph.add(Expr::new(Math::Ubnd, smallvec![wild.id, aj.id, agg.id]));

        vec![ubd]
    }
}

impl Applier<Math, Meta> for LASall {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&self.a][0];
        let a_schema = egraph[a].metadata.clone().schema.unwrap();

        let (a_i, a_j) =
            if let Schema::Mat(arow, acol)
            = a_schema {
                (arow, acol)
            } else {
                panic!("wrong schema in ladd")
            };

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsall_i".to_owned() + &fresh_s;
        let fresh_j = "vsall_j".to_owned() + &fresh_s;

        let bind_ai = if a_i == 1 {"_"} else { &fresh_i };
        let bind_aj = if a_j == 1 {"_"} else { &fresh_j };

        let bind_wild = "_";

        // (sum i (sum j [i,j] A))
        let ai = egraph.add(Expr::new(Math::Str(bind_ai.to_owned()), smallvec![]));
        let aj = egraph.add(Expr::new(Math::Str(bind_aj.to_owned()), smallvec![]));
        let wild = egraph.add(Expr::new(Math::Str(bind_wild.to_owned()), smallvec![]));

        let a = egraph.add(Expr::new(Math::Bind, smallvec![ai.id, aj.id, a]));

        let j_dim = egraph.add(Expr::new(Math::Num(a_j as i32), smallvec![]));
        let agg_j_dim = egraph.add(Expr::new(Math::Dim, smallvec![aj.id, j_dim.id]));

        let i_dim = egraph.add(Expr::new(Math::Num(a_i as i32), smallvec![]));
        let agg_i_dim = egraph.add(Expr::new(Math::Dim, smallvec![ai.id, i_dim.id]));

        let aggi = egraph.add(Expr::new(Math::Agg, smallvec![agg_i_dim.id, a.id]));
        let aggj = egraph.add(Expr::new(Math::Agg, smallvec![agg_j_dim.id, aggi.id]));

        let ubd = egraph.add(Expr::new(Math::Ubnd, smallvec![wild.id, wild.id, aggj.id]));

        vec![ubd]
    }
}

//Math::parse_pattern("(b+ ?k ?l (b- ?i ?j ?x))").unwrap(),
impl Applier<Math, Meta> for LABind {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let i = map[&self.i][0];
        let j = map[&self.j][0];
        let k = map[&self.k][0];
        let l = map[&self.l][0];
        let x = map[&self.x][0];

        let i_schema = egraph[i].metadata.clone().schema.unwrap();
        let j_schema = egraph[j].metadata.clone().schema.unwrap();
        let k_schema = egraph[k].metadata.clone().schema.unwrap();
        let l_schema = egraph[l].metadata.clone().schema.unwrap();
        let x_schema = egraph[x].metadata.clone().schema.unwrap();

        let (i_s, j_s, k_s, l_s) =
            if let (Schema::Name(i), Schema::Name(j), Schema::Name(k), Schema::Name(l))
            = (i_schema, j_schema, k_schema, l_schema) {
                (i, j, k, l)
            } else {
                panic!("wrong schema in ladd")
            };

        let (x_i, x_j) =
            if let Schema::Schm(schema) = x_schema {
                (*schema.get(&i_s).unwrap(), *schema.get(&j_s).unwrap())
            } else {
                panic!("wrong schema in labind")
            };

        if l_s == "_" {
            assert_eq!(j_s, "_", "unbinding wildcard");
        }
        if k_s == "_" {
            assert_eq!(i_s, "_", "unbinding wildcard");
        }

        // (subst l j (subst k i x))

        let i_n = egraph.add(Expr::new(Math::Num(x_i as i32), smallvec![]));
        let j_n = egraph.add(Expr::new(Math::Num(x_j as i32), smallvec![]));

        let i_dim = egraph.add(Expr::new(Math::Dim, smallvec![i, i_n.id]));
        let j_dim = egraph.add(Expr::new(Math::Dim, smallvec![j, j_n.id]));
        let k_dim = egraph.add(Expr::new(Math::Dim, smallvec![k, i_n.id]));
        let l_dim = egraph.add(Expr::new(Math::Dim, smallvec![l, j_n.id]));

        let sub_k_i_x = egraph.add(Expr::new(Math::Sub, smallvec![k_dim.id, i_dim.id, x]));
        let sub_l_j = egraph.add(Expr::new(Math::Sub, smallvec![l_dim.id, j_dim.id, sub_k_i_x.id]));

        vec![sub_l_j]
    }
}

impl Applier<Math, Meta> for LAMatBind {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let i = map[&self.i][0];
        let j = map[&self.j][0];
        let k = map[&self.k][0];
        let l = map[&self.l][0];
        let x = map[&self.x][0];
        let z = map[&self.z][0];

        let i_schema = egraph[i].metadata.clone().schema.unwrap();
        let j_schema = egraph[j].metadata.clone().schema.unwrap();
        let k_schema = egraph[k].metadata.clone().schema.unwrap();
        let l_schema = egraph[l].metadata.clone().schema.unwrap();

        let (i_s, j_s, k_s, l_s) =
            if let (Schema::Size(i), Schema::Size(j), Schema::Name(k), Schema::Name(l))
            = (i_schema, j_schema, k_schema, l_schema) {
                (i, j, k, l)
            } else {
                panic!("wrong schema in ladd")
            };

        if l_s == "_" {
            assert_eq!(j_s, 1, "unbinding wildcard");
        }
        if k_s == "_" {
            assert_eq!(i_s, 1, "unbinding wildcard");
        }

        // (mat x k l nnz)
        let k_dim = egraph.add(Expr::new(Math::Dim, smallvec![k, i]));
        let l_dim = egraph.add(Expr::new(Math::Dim, smallvec![l, j]));
        let res = egraph.add(Expr::new(Math::Mat, smallvec![x, k_dim.id, l_dim.id, z]));

        vec![res]
    }
}
