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
        drw("ra-mul", "(* ?a ? b)", RAMul),
        drw("ra-add", "(+ ?a ?b)", RAAdd),
        drw("ra-mmul", "(sum ?j (* ?a ?b))", RAMMul),
        drw("ra-sum", "(sum ?i ?x)", RASum)
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
        drw("agg-subst", "(subst ?e ?v1 (sum ?v2 ?body))", SubstAgg),
        drw("la_mul", "(l* ?x ?y)", LAMul),
        drw("la_add", "(l+ ?x ?y)", LAAdd),
        drw("la_mmul","(m* ?x ?y)", LAMMul),
        drw("la-trans", "(trans ?a)", LATrans),
        drw("la-srow", "(srow ?a)", LASrow),
        drw("la-scol", "(scol ?a)", LAScol),
        drw("la-sall","(sall ?a)", LASall),
        drw("la-bind", "(b+ ?k ?l (b- ?i ?j ?x))", LABind),
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


        drw("agg-subst", "(subst ?e ?v1 (sum ?v2 ?body))", SubstAgg),
        drw("sum_i_a", "(sum ?i ?a)", SumIA),
        drw("pullup_mul", "(sum ?i (* ?a ?b))", PullMul),
        drw("pushdown_mul", "(* ?a (sum ?i ?b))", PushMul),
        drw("dim_subst", "(subst ?e (dim ?v ?m) (dim ?i ?n))", DimSubst)
    ]
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

        // [-i,k] (sum j (* [i,j]A [j,k]B))

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
                    i=&ubnd_i, k=&ubnd_k, j=&agg_j, xi=&bind_xi, xj=&bind_xj, yj=&bind_yj, yk=&bind_yk, j_n=*x_j as i32
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
        let (x_i, x_j) = (*x_schema.get(i_schema).unwrap(), *x_schema.get(j_schema).unwrap());

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

        let add_schema = egraph[add.id].metadata.schema.as_ref().unwrap();

        let m_s = add_schema.get_schm();

        let mut res = vec![];

        match m_s.len() {
            0 => {
                let mut bind = Math::parse_pattern(
                    "(b+ _ _ (+ (b- _ _ ?a) (b- _ _ ?b)))"
                ).unwrap().apply(egraph, map);
                res.append(&mut bind);
            },
            1 => {
                let i = m_s.keys().nth(0).unwrap().clone();

                let mut bind_i = Math::parse_pattern(
                    &format!(
                        "(b+ {i} _ (+ (b- {i} _ ?a) (b- {i} _ b)))",
                        i=&i
                    )
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_i);

                let mut bind_j = Math::parse_pattern(
                    &format!(
                        "(b+ _ {j} (+ (b- _ {j} ?a) (b- _ {j} b)))",
                        j=&i
                    )
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_j);
            },
            2 => {
                let ks: Vec<_> = m_s.keys().collect();
                let (i, j) = (ks[0].clone(), ks[1].clone());

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
            _ => {
                // do nothing
            }
        }
        res
    }
}

#[derive(Debug)]
struct RAMul;

impl Applier<Math, Meta> for RAMul {
    fn apply(&self, egraph: &mut EGraph, map: &WildMap) -> Vec<AddResult> {
        let a = map[&"?a".parse().unwrap()][0];
        let b = map[&"?b".parse().unwrap()][0];
        let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, b]));

        let mul_schema = egraph[mul.id].metadata.schema.as_ref().unwrap();

        let m_s = mul_schema.get_schm();

        let mut res = vec![];

        match m_s.len() {
            0 => {
                let mut bind = Math::parse_pattern(
                    "(b+ _ _ (* (b- _ _ ?a) (b- _ _ ?b)))"
                ).unwrap().apply(egraph, map);
                res.append(&mut bind);
            },
            1 => {
                let i = m_s.keys().nth(0).unwrap().clone();

                let mut bind_i = Math::parse_pattern(
                    &format!(
                        "(b+ {i} _ (* (b- {i} _ ?a) (b- {i} _ b)))",
                        i=&i
                    )
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_i);

                let mut bind_j = Math::parse_pattern(
                    &format!(
                        "(b+ _ {j} (* (b- _ {j} ?a) (b- _ {j} b)))",
                        j=&i
                    )
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_j);
            },
            2 => {
                let ks: Vec<_> = m_s.keys().collect();
                let (i, j) = (ks[0].clone(), ks[1].clone());

                let mut bind_ij = Math::parse_pattern(
                    &format!(
                        "(b+ {i} {j} (* (b- {i} {j} ?a) (b- {i} {j} b)))",
                        i=&i, j=&j
                    )
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_ij);

                let mut bind_ji = Math::parse_pattern(
                    &format!(
                        "(b+ {j} {i} (* (b- {j} {i} ?a) (b- {j} {i} b)))",
                        i=&i, j=&j
                    )
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_ji);
            }
            _ => {
                // do nothing
            }
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
            match schema.len() {
                0 => {
                    let mut bu = Math::parse_pattern(
                        "(b+ _ _ (b- _ _ ?e))"
                    ).unwrap().apply(egraph, map);
                    res.append(&mut bu);
                },
                1 => {
                    let i = schema.keys().nth(0).unwrap();

                    let mut bu_iw = Math::parse_pattern(
                        &format!("(b+ {i} _ (b- {i} _ ?e))", i=i)
                    ).unwrap().apply(egraph, map);
                    res.append(&mut bu_iw);

                    // TODO not done here!!!
                    //let k = ks[0].clone();

                    //let i = egraph.add(Expr::new(Math::Str(k), smallvec![]));
                    //let wild = egraph.add(Expr::new(Math::Str("_".to_owned()), smallvec![]));

                    //let ubnd_i = egraph.add(Expr::new(Math::Ubnd, smallvec![i.id, wild.id, e ]));
                    //let bind_i = egraph.add(Expr::new(Math::Bind, smallvec![i.id, wild.id, ubnd_i.id]));

                    //let ubnd_j = egraph.add(Expr::new(Math::Ubnd, smallvec![wild.id, i.id, e]));
                    //let bind_j = egraph.add(Expr::new(Math::Bind, smallvec![wild.id, i.id, ubnd_j.id]));

                    //res.push(bind_i);
                    //res.push(bind_j);
                },
                2 => {
                    // bind ubnd i,j j,i
                    let ks: Vec<_> = schema.keys().collect();
                    let (i, j) = (ks[0].clone(), ks[1].clone());

                    let i = egraph.add(Expr::new(Math::Str(i), smallvec![]));
                    let j = egraph.add(Expr::new(Math::Str(j), smallvec![]));

                    let ubnd_ij = egraph.add(Expr::new(Math::Ubnd, smallvec![i.id, j.id, e]));
                    let bind_ij = egraph.add(Expr::new(Math::Bind, smallvec![i.id, j.id, ubnd_ij.id]));

                    let ubnd_ji = egraph.add(Expr::new(Math::Ubnd, smallvec![j.id, i.id, e]));
                    let bind_ji = egraph.add(Expr::new(Math::Bind, smallvec![j.id, i.id, ubnd_ji.id]));

                    res.push(bind_ji);
                    res.push(bind_ij);
                },
                _ => {
                    // do nothing
                }
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

        let j_schema = egraph[j].metadata.schema.as_ref().unwrap();
        let sum_schema = egraph[sum.id].metadata.schema.as_ref().unwrap();

        // SUM j (* A B) =>  (m* A[-i j] B[-j k]) [i, k]

        let schema = sum_schema.get_schm();

        let j_s = j_schema.get_dims().0.clone();

        let mut res = vec![];

        match schema.len() {
            0 => {
                let mut bind = Math::parse_pattern(
                    &format!("(b+ _ _ (m* (b- _ {j} ?a) (b- {j} _ ?b)))", j=&j_s)
                ).unwrap().apply(egraph, map);

                res.append(&mut bind);
            },
            1 => {
                let k = schema.keys().nth(0).unwrap().clone();

                let mut bind_iw = Math::parse_pattern(
                    &format!("(b+ {i} _ (m* (b- {i} {j} ?a) (b- {j} _ ?b)))", i=&k, j=&j_s)
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_iw);

                let mut bind_wi = Math::parse_pattern(
                    &format!("(b+ _ {j} (m* (b- _ {j} ?a) (b- {j} {i} ?b)))", i=&k, j=&j_s)
                ).unwrap().apply(egraph, map);
                res.append(&mut bind_wi);
            },
            2 => {
                let ks: Vec<_> = schema.keys().collect();
                let (i, k) = (ks[0].clone(), ks[1].clone());

                let mut bind = Math::parse_pattern(
                    &format!("(b+ {i} {k} (m* (b- {i} {j} ?a) (b- {j} {k} ?b)))", i=&i, j=&j_s, k=&k)
                ).unwrap().apply(egraph, map);
                res.append(&mut bind);
            }
            _ => {
                // do nothing
            }
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
        let schema = egraph[sum.id].metadata.schema.as_ref().unwrap().get_schm();

        let mut res = vec![];
        match schema.len() {
            0 => {
                let mut scol = Math::parse_pattern(
                    &format!("(b+ _ _ (scol (b- {i} _ ?x)))", i=&i_s)
                ).unwrap().apply(egraph, map);
                res.append(&mut scol);

                let mut srow = Math::parse_pattern(
                    &format!("(b+ _ _ (srow (b- _ {i} ?x)))", i=&i_s)
                ).unwrap().apply(egraph, map);
                res.append(&mut srow);
            },
            1 => {
                let j = schema.keys().nth(0).unwrap().clone();

                let mut scol = Math::parse_pattern(
                    &format!("(b+ _ {j} (scol (b- {i} {j} ?x)))", j=&j, i=&i_s)
                ).unwrap().apply(egraph, map);
                res.append(&mut scol);

                let mut srow = Math::parse_pattern(
                    &format!("(b+ {i} _ (srow (b- {j} {i} ?x)))", j=&j, i=&i_s)
                ).unwrap().apply(egraph, map);
                res.append(&mut srow);
            },
            _ => {
                // a sum with more than 2 schemas
                // cannot be an LA expression
            }
        }
        res
    }
}
