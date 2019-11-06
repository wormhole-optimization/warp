use crate::{Math, Meta, EGraph, Schema};

use egg::{
    egraph::{AddResult},
    expr::Expr,
    parse::ParsableLanguage,
    pattern::{Applier, Rewrite, WildMap},
};

use smallvec::smallvec;
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

fn rw(name: &str, l: &str, r: &str) -> Rewrite<Math, Meta> {
    Math::parse_rewrite::<Meta>(name, l, r).unwrap()
}

fn drw(name: &str, l: &str, r: impl Applier<Math, Meta> + 'static) -> Rewrite<Math, Meta>
{
    Rewrite::new(
        name,
        Math::parse_pattern(l).unwrap(),
        r
    )
}

#[rustfmt::skip]
pub fn untrans_rules() -> Vec<Rewrite<Math, Meta>> {
    vec![
        rw("ra-minus", "(l+ ?a (l* (lit -1) ?b))" ,"(l- ?a ?b)"),
        rw("ra-elim-bind", "(b- ?i ?j (b+ ?i ?j ?x))", "?x"),
        rw("ra_transpose", "(b- ?j ?i (b+ ?i ?j ?x))", "(trans ?x)"),
        rw("ra_sall", "(srow (scol ?x))", "(sall ?x)"),
        rw("ra_sall2", "(scol (srow ?x))", "(sall ?x)"),
        drw("ra-bind", "?e", RABind),
        drw("ra-add", "(+ ?a ?b)", RAAdd),
        drw("ra-mul", "(* ?a ?b)", RAMul),
        drw("ra-sum", "(sum ?i ?x)", RASum),
        drw("ra-mmul", "(sum ?j (* ?a ?b))", RAMMul),
    ]
}

#[rustfmt::skip]
pub fn trans_rules() -> Vec<Rewrite<Math, Meta>> {
    vec![
        rw("la-minus", "(l- ?a ?b)", "(l+ ?a (l* (lit -1) ?b))"),
        rw("la-mat-bind", "(b+ ?k ?l (lmat ?x ?i ?j ?z))", "(mat ?x (dim ?k ?i) (dim ?l ?j) ?z)"),
        rw("la-lit-bind",  "(b+ ?i ?j (llit ?n))",            "(lit ?n)"),
        rw("subst-+",      "(subst ?e ?v (+ ?a ?b))",         "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw("subst-*",      "(subst ?e ?v (* ?a ?b))",         "(* (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw("subst-matrix", "(subst ?e ?v (mat ?a ?i ?j ?z))", "(mat ?a (subst ?e ?v ?i) (subst ?e ?v ?j) ?z)"),
        rw("subst-lit",    "(subst ?e ?v (lit ?n))",          "(lit ?n)"),
        rw("subst-var",    "(subst ?e ?v (var ?n))",          "(var ?n)"),
        drw("la_mul", "(l* ?x ?y)", LAMul),
        drw("la_add", "(l+ ?x ?y)", LAAdd),
        drw("la_mmul","(m* ?x ?y)", LAMMul),
        drw("la-srow", "(srow ?a)", LASrow),
        drw("la-scol", "(scol ?a)", LAScol),
        drw("la-sall", "(sall ?a)", LASall),
        drw("la-trans", "(trans ?a)", LATrans),
        drw("la-bind", "(b+ ?k ?l (b- ?i ?j ?x))", LABind),
        drw("agg-subst", "(subst ?e ?v1 (sum ?v2 ?body))", SubstAgg),
        drw("dim_subst", "(subst ?e (dim ?v ?m) (dim ?i ?n))", DimSubst)
    ]
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite<Math, Meta>> {
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
        drw("sum_i_a", "(sum ?i ?a)", SumIA),
        drw("pullup_mul", "(sum ?i (* ?a ?b))", PullMul),
        drw("pushdown_mul", "(* ?a (sum ?i ?b))", PushMul),
        drw("agg-subst", "(subst ?e ?v1 (sum ?v2 ?body))", SubstAgg),
        drw("dim_subst", "(subst ?e (dim ?v ?m) (dim ?i ?n))", DimSubst),
        drw("foundit",
            "(+ (sum ?i (sum ?j (+ (* (mat ?x ?i ?j ?za) (mat ?x ?i ?j ?zb)) (+ \
             (* (mat ?x ?i ?j ?zc) (sum ?k (* (mat ?u ?i ?k ?zd) (mat ?v ?k ?j ?ze)))) \
             (* (mat ?x ?i ?j ?zf) (sum ?k (* (mat ?u ?i ?k ?zg) (mat ?v ?k ?j ?zh)))))))) \
             (sum ?c (sum ?a (* \
             (sum ?b (* (mat ?u ?a ?b ?zi) (mat ?u ?b ?c ?zj)))\
             (sum ?d (* (mat ?v ?a ?d ?zk) (mat ?v ?d ?c ?zl)))))))",
            Foundit
        )
    ]
}

#[derive(Debug)]
struct Foundit;

impl Applier<Math, Meta> for Foundit {
    fn apply(&self, _egraph: &mut EGraph, _map: &WildMap) -> Vec<AddResult> {
        panic!("FOUNDITTT")
    }
}

#[derive(Debug)]
struct SubstAgg;

impl Applier<Math, Meta> for SubstAgg {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let v1 = map[&"?v1".parse().unwrap()][0];
        let v2 = map[&"?v2".parse().unwrap()][0];
        let e = map[&"?e".parse().unwrap()][0];
        let body = map[&"?body".parse().unwrap()][0];

        let res = if v1 == v2 {
            egraph.add(Expr::new(Math::Agg, smallvec![v2, body]))
        } else {
            let sub_body = egraph.add(Expr::new(Math::Sub, smallvec![e, v1, body]));
            egraph.add(Expr::new(Math::Agg, smallvec![v2, sub_body.id]))
        };

        vec![res]
    }
}

#[derive(Debug)]
struct SumIA;
impl Applier<Math, Meta> for SumIA {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let i = map[&"?i".parse().unwrap()][0];
        let i_m = &egraph[i].metadata;
        let (k, n) = i_m.schema.as_ref().unwrap().get_dims();

        let a = map[&"?a".parse().unwrap()][0];
        let a_m = &egraph[a].metadata;
        let body = a_m.schema.as_ref().unwrap().get_schm();

        if !body.contains_key(k) {
            Math::parse_pattern(
                &format!("(* ?a (lit {n}))", n=*n as i32)
            ).unwrap().apply(egraph, map)
        } else {
            vec![]
        }
    }
}

#[derive(Debug)]
struct PullMul;

impl Applier<Math, Meta> for PullMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let i = map[&"?i".parse().unwrap()][0];
        let i_schema = &egraph[i].metadata;
        let k = i_schema.schema.as_ref().unwrap().get_dims().0;

        let a = map[&"?a".parse().unwrap()][0];
        let a_schema = &egraph[a].metadata;
        let body = a_schema.schema.as_ref().unwrap().get_schm();

        if !body.contains_key(k) {
            Math::parse_pattern(
                "(* ?a (sum ?i ?b))"
            ).unwrap().apply(egraph, map)
        } else {
            vec![]
        }
    }
}

#[derive(Debug)]
struct PushMul;
impl Applier<Math, Meta> for PushMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&"?a".parse().unwrap()][0];
        let i = map[&"?i".parse().unwrap()][0];
        let b = map[&"?b".parse().unwrap()][0];

        let (i_s, i_n) = egraph[i].metadata.schema.as_ref().unwrap().get_dims();
        let a_schema = egraph[a].metadata.schema.as_ref().unwrap().get_schm();

        if !a_schema.contains_key(i_s) {
            Math::parse_pattern(
                "(sum ?i (* ?a ?b))"
            ).unwrap().apply(egraph, map)
        } else {
            let mut s = DefaultHasher::new();
            [i, a, b].hash(&mut s);
            let fresh_s = format!("v{s}", s=&(s.finish() % 976521).to_string());

            Math::parse_pattern(
                &format!(
                    "(sum (dim {fv} {fn}) (* ?a (subst (dim {fv} {fn}) ?i ?b)))",
                    fv=&fresh_s, fn=*i_n as i32
                )
            ).unwrap().apply(egraph, map)
        }
    }
}

#[derive(Debug)]
struct DimSubst;
impl Applier<Math, Meta> for DimSubst {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let e = map[&"?e".parse().unwrap()][0];
        let v = map[&"?v".parse().unwrap()][0];
        let i = map[&"?i".parse().unwrap()][0];
        let n = map[&"?n".parse().unwrap()][0];

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

#[derive(Debug)]
struct LAMul;

impl Applier<Math, Meta> for LAMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let x = map[&"?x".parse().unwrap()][0];
        let y = map[&"?y".parse().unwrap()][0];
        let x_schema = egraph[x].metadata.clone().schema.unwrap();
        let (x_i, x_j) = x_schema.get_mat();
        let y_schema = egraph[y].metadata.clone().schema.unwrap();
        let (y_i, y_j) = y_schema.get_mat();

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = format!("vmul_i{}", &fresh_s);
        let fresh_j = format!("vmul_j{}", &fresh_s);

        let bind_xi = if *x_i == 1 {"_"} else { &fresh_i };
        let bind_xj = if *x_j == 1 {"_"} else { &fresh_j };
        let bind_yi = if *y_i == 1 {"_"} else { &fresh_i };
        let bind_yj = if *y_j == 1 {"_"} else { &fresh_j };
        let ubnd_i = if x_i * y_i == 1 {"_"} else { &fresh_i };
        let ubnd_j = if x_j * y_j == 1 {"_"} else { &fresh_j };

        Math::parse_pattern(
            &format!(
                "(b- {i} {j} (* (b+ {xi} {xj} ?x) (b+ {yi} {yj} ?y)))",
                i=ubnd_i, j=ubnd_j, xi=bind_xi, xj=bind_xj, yi=bind_yi, yj=bind_yj
            )).unwrap().apply(egraph, map)
    }
}

#[derive(Debug)]
struct LAAdd;

impl Applier<Math, Meta> for LAAdd {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let x = map[&"?x".parse().unwrap()][0];
        let y = map[&"?y".parse().unwrap()][0];

        let x_schema = egraph[x].metadata.clone().schema.unwrap();
        let y_schema = egraph[y].metadata.clone().schema.unwrap();

        let (x_i, x_j) = x_schema.get_mat();
        let (y_i, y_j) = y_schema.get_mat();

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vadd_i".to_owned() + &fresh_s;
        let fresh_j = "vadd_j".to_owned() + &fresh_s;

        let bind_xi = if *x_i == 1 {"_"} else { &fresh_i };
        let bind_xj = if *x_j == 1 {"_"} else { &fresh_j };
        let bind_yi = if *y_i == 1 {"_"} else { &fresh_i };
        let bind_yj = if *y_j == 1 {"_"} else { &fresh_j };

        let ubnd_i = if x_i * y_i == 1 {"_"} else { &fresh_i };
        let ubnd_j = if x_j * y_j == 1 {"_"} else { &fresh_j };

        // [-i,j] (* [i,j]A [i,j]B)
        Math::parse_pattern(
            &format!(
                "(b- {i} {j} (* (b+ {xi} {xj} ?x) (b+ {yi} {yj} ?y)))",
                i=&ubnd_i, j=&ubnd_j, xi=&bind_xi, xj=&bind_xj, yi=&bind_yi, yj=&bind_yj
            )
        ).unwrap().apply(egraph, map)
    }
}

#[derive(Debug)]
struct LAMMul;
impl Applier<Math, Meta> for LAMMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let x = map[&"?x".parse().unwrap()][0];
        let y = map[&"?y".parse().unwrap()][0];

        let x_schema = egraph[x].metadata.clone().schema.unwrap();
        let y_schema = egraph[y].metadata.clone().schema.unwrap();

        let (x_i, x_j) = x_schema.get_mat();
        let (y_j, y_k) = y_schema.get_mat();


        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vmmul_i".to_owned() + &fresh_s;
        let fresh_j = "vmmul_j".to_owned() + &fresh_s;
        let fresh_k = "vmmul_k".to_owned() + &fresh_s;

        let bind_xi = if *x_i == 1 {"_"} else { &fresh_i };
        let bind_xj = if *x_j == 1 {"_"} else { &fresh_j };
        let bind_yj = if *y_j == 1 {"_"} else { &fresh_j };
        let bind_yk = if *y_k == 1 {"_"} else { &fresh_k };

        let ubnd_i = if *x_i == 1 {"_"} else { &fresh_i };
        let ubnd_k = if *y_k == 1 {"_"} else { &fresh_k };

        let agg_j = if x_j * y_j == 1 {"_"} else {&fresh_j};

        if agg_j == "_" {
            Math::parse_pattern(
                &format!(
                    "(b- {i} {k} (* (b+ {xi} {xj} ?x) (b+ {yj} {yk} ?y)))",
                    i=&ubnd_i, k=&ubnd_k, xi=&bind_xi, xj=&bind_xj, yj=&bind_yj, yk=&bind_yk
                )
            ).unwrap().apply(egraph, map)
        } else {
            Math::parse_pattern(
                &format!(
                    "(b- {i} {k} (sum (dim {j} {j_n}) (* (b+ {xi} {xj} ?x) (b+ {yj} {yk} ?y))))",
                    i=&ubnd_i, k=&ubnd_k, j=&agg_j, j_n=*x_j as i32,
                    xi=&bind_xi, xj=&bind_xj, yj=&bind_yj, yk=&bind_yk,
                )
            ).unwrap().apply(egraph, map)
        }
    }
}

#[derive(Debug)]
struct LATrans;

impl Applier<Math, Meta> for LATrans {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&"?a".parse().unwrap()][0];
        let a_schema = egraph[a].metadata.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vtrans_i".to_owned() + &fresh_s;
        let fresh_j = "vtrans_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 {"_"} else { &fresh_i };
        let bind_aj = if *a_j == 1 {"_"} else { &fresh_j };

        Math::parse_pattern(
            &format!(
                "(b- {j} {i} (b+ {i} {j} ?a))",
                j=&bind_aj, i=&bind_ai
            )
        ).unwrap().apply(egraph, map)
    }
}

#[derive(Debug)]
struct LASrow;

impl Applier<Math, Meta> for LASrow {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&"?a".parse().unwrap()][0];
        let a_schema = egraph[a].metadata.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsrow_i".to_owned() + &fresh_s;
        let fresh_j = "vsrow_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 {"_"} else { &fresh_i };
        let bind_aj = if *a_j == 1 {"_"} else { &fresh_j };

        Math::parse_pattern(
            &format!(
                "(b- _ {j} (sum (dim {i} {in}) (b+ {i} {j} ?a)))",
                i=&bind_ai, in=*a_i as i32, j=&bind_aj
            )
        ).unwrap().apply(egraph, map)
    }
}

#[derive(Debug)]
struct LAScol;

impl Applier<Math, Meta> for LAScol {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&"?a".parse().unwrap()][0];
        let a_schema = egraph[a].metadata.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsrow_i".to_owned() + &fresh_s;
        let fresh_j = "vsrow_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 {"_"} else { &fresh_i };
        let bind_aj = if *a_j == 1 {"_"} else { &fresh_j };

        Math::parse_pattern(
            &format!(
                "(b- {i} _ (sum (dim {j} {jn}) (b+ {i} {j} ?a)))",
                i=&bind_ai, jn=*a_j as i32, j=&bind_aj
            )
        ).unwrap().apply(egraph, map)
    }
}

#[derive(Debug)]
struct LASall;

impl Applier<Math, Meta> for LASall {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&"?a".parse().unwrap()][0];
        let a_schema = egraph[a].metadata.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsall_i".to_owned() + &fresh_s;
        let fresh_j = "vsall_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 {"_"} else { &fresh_i };
        let bind_aj = if *a_j == 1 {"_"} else { &fresh_j };

        Math::parse_pattern(
            &format!(
                "(b- _ _ (sum (dim {i} {in}) (sum (dim {j} {jn}) (b+ {i} {j} ?a))))",
                i=&bind_ai, in=*a_i as i32, j=&bind_aj, jn=*a_j as i32
            )
        ).unwrap().apply(egraph, map)
    }
}

#[derive(Debug)]
struct LABind;

impl Applier<Math, Meta> for LABind {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let i = map[&"?i".parse().unwrap()][0];
        let j = map[&"?j".parse().unwrap()][0];
        let k = map[&"?k".parse().unwrap()][0];
        let l = map[&"?l".parse().unwrap()][0];
        let x = map[&"?x".parse().unwrap()][0];

        let i_schema = egraph[i].metadata.schema.as_ref().unwrap().get_name();
        let j_schema = egraph[j].metadata.schema.as_ref().unwrap().get_name();
        let k_schema = egraph[k].metadata.schema.as_ref().unwrap().get_name();
        let l_schema = egraph[l].metadata.schema.as_ref().unwrap().get_name();
        let x_schema = egraph[x].metadata.schema.as_ref().unwrap().get_schm();
        let (x_i, x_j) = (*x_schema.get(i_schema).unwrap_or(&1), *x_schema.get(j_schema).unwrap_or(&1));

        if l_schema == "_" {
            assert_eq!(j_schema, "_", "unbinding wildcard");
        }
        if k_schema == "_" {
            assert_eq!(i_schema, "_", "unbinding wildcard");
        }

        Math::parse_pattern(
            &format!(
                "(subst (dim {l} {jn}) (dim {j} {jn}) (subst (dim {k} {in}) (dim {i} {in}) ?x))",
                l=&l_schema.clone(), jn=x_j as i32, j=&j_schema.clone(),
                k=&k_schema.clone(), in=x_i as i32, i=&i_schema.clone()
            )
        ).unwrap().apply(egraph, map)
    }
}

#[derive(Debug)]
struct RAAdd;

impl Applier<Math, Meta> for RAAdd {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&"?a".parse().unwrap()][0];
        let b = map[&"?b".parse().unwrap()][0];
        let add = egraph.add(Expr::new(Math::Add, smallvec![a, b]));
        let mut add_schema = egraph[add.id].metadata.schema.as_ref().unwrap().get_schm().keys();

        let mut res = vec![];
        if add_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = add_schema.next().unwrap_or(&wc).clone();
            let j = add_schema.next().unwrap_or(&wc).clone();

            let mut bind_ij = Math::parse_pattern(
                &format!(
                    "(b+ {i} {j} (+ (b- {i} {j} ?a) (b- {i} {j} b)))",
                    i=&i, j=&j
                )
            ).unwrap().apply(egraph, map);
            res.append(&mut bind_ij);

            let mut bind_ji = Math::parse_pattern(
                &format!(
                    "(b+ {j} {i} (+ (b- {j} {i} ?a) (b- {j} {i} b)))",
                    i=&i, j=&j
                )
            ).unwrap().apply(egraph, map);
            res.append(&mut bind_ji);
        }
        res
    }
}

#[derive(Debug)]
struct RAMul;

impl Applier<Math, Meta> for RAMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&"?a".parse().unwrap()][0];
        let mut a_schema = egraph[a].metadata.schema.as_ref().unwrap().get_schm().keys();
        let b = map[&"?b".parse().unwrap()][0];
        let mut b_schema = egraph[b].metadata.schema.as_ref().unwrap().get_schm().keys();
        let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, b]));
        let mut mul_schema = egraph[mul.id].metadata.schema.as_ref().unwrap().get_schm().keys();

        let mut res = vec![];
        if mul_schema.len() <= 2 {
            // TODO check if a schema contains the other
            let wc = "_".to_owned();
            let i = mul_schema.next().unwrap_or(&wc).clone();
            let j = mul_schema.next().unwrap_or(&wc).clone();
            let ai = a_schema.next().unwrap_or(&wc).clone();
            let aj = a_schema.next().unwrap_or(&wc).clone();
            let bi = b_schema.next().unwrap_or(&wc).clone();
            let bj = b_schema.next().unwrap_or(&wc).clone();

            let mut bind_ij = Math::parse_pattern(
                &format!(
                    "(b+ {i} {j} (l* (b- {i} {j} ?a) (b- {i} {j} ?b)))",
                    i=&i, j=&j
                )
            ).unwrap().apply(egraph, map);
            res.append(&mut bind_ij);

            let mut bind_ji = Math::parse_pattern(
                &format!(
                    "(b+ {j} {i} (l* (b- {j} {i} ?a) (b- {j} {i} ?b)))",
                    i=&i, j=&j
                )
            ).unwrap().apply(egraph, map);
            res.append(&mut bind_ji);

            let mut mmul_ij = Math::parse_pattern(
                &format!(
                    "(b+ {i} {j} (m* (b- {i} _ ?a) (b- _ {j} ?b)))",
                    i=&i, j=&j
                )
            ).unwrap().apply(egraph, map);
            res.append(&mut mmul_ij);

            let mut mmul_ji = Math::parse_pattern(
                &format!(
                    "(b+ {j} {i} (m* (b- {j} _ ?a) (b- _ {i} ?b)))",
                    i=&i, j=&j
                )
            ).unwrap().apply(egraph, map);
            res.append(&mut mmul_ji);
        }
        res
    }
}

#[derive(Debug)]
struct RABind;

impl Applier<Math, Meta> for RABind {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let e = map[&"?e".parse().unwrap()][0];

        let mut res = Vec::new();
        if let Some(Schema::Schm(schema)) = egraph[e].metadata.schema.as_ref() {
            let mut schema = schema.keys();
            if schema.len() <= 2 {
                let wc = "_".to_owned();
                let i = schema.next().unwrap_or(&wc).clone();
                let j = schema.next().unwrap_or(&wc).clone();

                let mut bind_ij = Math::parse_pattern(
                    &format!("(b+ {i} {j} (b- {i} {j} ?e))", i=i, j=j)
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_ij);

                let mut bind_ji = Math::parse_pattern(
                    &format!("(b+ {j} {i} (b- {j} {i} ?e))", i=i, j=j)
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_ji);
            }
        }
        res
    }
}

#[derive(Debug)]
struct RAMMul;

impl Applier<Math, Meta> for RAMMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&"?a".parse().unwrap()][0];
        let b = map[&"?b".parse().unwrap()][0];
        let j = map[&"?j".parse().unwrap()][0];
        let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, b]));
        let sum = egraph.add(Expr::new(Math::Agg, smallvec![j, mul.id]));
        let j_schema = egraph[j].metadata.schema.as_ref().unwrap().get_dims().0.clone();
        let mut sum_schema = egraph[sum.id].metadata.schema.as_ref().unwrap().get_schm().keys();

        let mut res = vec![];
        if sum_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = sum_schema.next().unwrap_or(&wc).clone();
            let k = sum_schema.next().unwrap_or(&wc).clone();

            let mut bind_ik = Math::parse_pattern(
                &format!("(b+ {i} {k} (m* (b- {i} {j} ?a) (b- {j} {k} ?b)))", i=&i, j=&j_schema, k=&k)
            ).unwrap().apply(egraph, map);
            res.append(&mut bind_ik);

            let mut bind_ki = Math::parse_pattern(
                &format!("(b+ {k} {i} (m* (b- {k} {j} ?a) (b- {j} {i} ?b)))", i=&i, j=&j_schema, k=&k)
            ).unwrap().apply(egraph, map);
            res.append(&mut bind_ki);
        }
        res
    }
}

#[derive(Debug)]
struct RASum;

impl Applier<Math, Meta> for RASum {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let i = map[&"?i".parse().unwrap()][0];
        let x = map[&"?x".parse().unwrap()][0];
        let i_s = egraph[i].metadata.schema.as_ref().unwrap().get_dims().0.clone();
        let sum = egraph.add(Expr::new(Math::Agg, smallvec![i, x]));
        let mut schema = egraph[sum.id].metadata.schema.as_ref().unwrap().get_schm().keys();

        let mut res = vec![];
        if schema.len() <= 1 {
            let wc = "_".to_owned();
            let j = schema.next().unwrap_or(&wc).clone();

            let mut scol = Math::parse_pattern(
                &format!("(b+ _ {j} (scol (b- {i} {j} ?x)))", j=&j, i=&i_s)
            ).unwrap().apply(egraph, map);
            res.append(&mut scol);

            let mut srow = Math::parse_pattern(
                &format!("(b+ {i} _ (srow (b- {j} {i} ?x)))", j=&j, i=&i_s)
            ).unwrap().apply(egraph, map);
            res.append(&mut srow);
        }
        res
    }
}
