use crate::{EGraph, Math};

use egg::expr::{Expr, Id, RecExpr};

use lp_modeler::solvers::{GurobiSolver, SolverTrait};
use lp_modeler::dsl::*;

use ordered_float::NotNan;
use bimap::BiMap;

use std::{
    collections::HashSet,
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

pub fn extract(egraph: EGraph,
               roots: &[Id],
               cost: fn(&EGraph, &Expr<Math, Id>) -> usize)
               -> Vec<RecExpr<Math>>
{
    let mut problem = LpProblem::new("wormhole", LpObjective::Minimize);

    // Create symbolic variables Bn (for each node) & Bq (each class)
    let mut var_bns = BiMap::<&Expr<Math, Id>, String>::new();
    let mut var_bqs = BiMap::<Id, String>::new();
    //let mut var_bij = HashMap::<(String, String), String>::new();

    for c in egraph.classes() {
        let bq = "bq".to_owned() + &c.id.to_string();
        var_bqs.insert(c.id, bq);

        for e in c.nodes.iter() {

            let mut s = DefaultHasher::new();
            e.hash(&mut s);
            let bn = "bn".to_owned() + &s.finish().to_string();

            var_bns
                .insert_no_overwrite(e, bn)
                .expect("equal exprs not merged");
        }
    };

    // Objective function to minimize
    let obj_vec: Vec<LpExpression> = {
        var_bns.iter().map(|(e, var)| {
            let coef = cost(&egraph, e);
            let bn = LpBinary::new(&var);
            coef as f32 * &bn
        }).collect()
    };

    problem += obj_vec.sum();

    // Constraint Br: must pick roots

    for root in roots {
        let br = LpBinary::new(&var_bqs.get_by_left(&root).unwrap());
        problem += (0 + &br).equal(1);
    }

    // Constraints Gq & Fn
    // Gq: Bq => OR Bn in q.nodes
    // Fn: Bn => AND Bq in n.children
    for class in egraph.classes() {
        // Gq <=> (1-Bq) + (sum Bn) > 0
        let bq = LpBinary::new(&var_bqs.get_by_left(&class.id).unwrap());
        let sum_bn = sum(&class.nodes, |n| {
            let bn = LpBinary::new(&var_bns.get_by_left(&n).unwrap());
            bn
        });
        problem += (1 - bq + sum_bn).ge(1);

        // Fn <=> AND_Bq . (1-Bn) + Bq > 0
        for node in class.iter() {
            let bn = LpBinary::new(&var_bns.get_by_left(&node).unwrap());
            for class in node.children.iter() {
                let bq = LpBinary::new(&var_bqs.get_by_left(&class).unwrap());
                problem += ((1 - &bn) + bq).ge(1);
            }
        }
    }

    let solver = GurobiSolver::new();
    let result = solver.run(&problem);

    let (_solver_status, var_values) = result.unwrap();

    // Lookup selected nodes and classes
    let mut selected = HashSet::new();

    for (var_name, var_value) in &var_values {
        let int_var_value = *var_value as u32;
        if int_var_value == 1 {
            if let Some(&v) = var_bns.get_by_right(&var_name) {
                selected.insert(v);
            } else {
                if let Some(&v) = var_bqs.get_by_right(&var_name) {
                    println!("{:?}", v)
                }
            }
        }
    }

    //println!("{:?}", selected);

    roots.iter().map(|root| find_expr(&egraph, *root, &selected)).collect()
}

fn find_expr(egraph: &EGraph, class: Id, selected: &HashSet<&Expr<Math, Id>>) -> RecExpr<Math> {
    let eclass = egraph.find(class);
    let best_node = egraph[eclass]
        .iter()
        .find(|n| selected.contains(n))
        .expect("no node selected in class");

    println!("{:?}", (class, best_node.clone()));

    best_node
        .clone()
        .map_children(|child| find_expr(egraph, child, selected))
        .into()
}

pub fn cost(egraph: &EGraph, expr: &Expr<Math, Id>) -> usize {
    match expr.op {
        Math::Add => {
            debug_assert_eq!(expr.children.len(), 2);
            let x = expr.children[0];
            let y = expr.children[1];

            let mut schema = egraph[x].metadata.schema.as_ref().unwrap().get_schm().clone();
            let y_schema = egraph[y].metadata.schema.as_ref().unwrap().get_schm().clone();

            let xs: HashSet<_> = schema.keys().collect();
            let ys: HashSet<_> = schema.keys().collect();

            let j: HashSet<_> = xs.intersection(&ys).collect();

            if j.is_empty() {
                10000000
            } else {
                schema.extend(y_schema);

                let x_sparsity = egraph[x].metadata.sparsity.unwrap();
                let y_sparsity = egraph[y].metadata.sparsity.unwrap();

                let sparsity = std::cmp::min(1.0.into(), x_sparsity + y_sparsity);

                let vol: usize = schema.values().product();
                let nnz = NotNan::from(vol as f64) * sparsity;
                nnz.round() as usize
            }
        },
        Math::Mul => {
            debug_assert_eq!(expr.children.len(), 2);
            let x = expr.children[0];
            let y = expr.children[1];

            let mut schema = egraph[x].metadata.schema.as_ref().unwrap().get_schm().clone();
            let y_schema = egraph[y].metadata.schema.as_ref().unwrap().get_schm().clone();
            schema.extend(y_schema);

            let x_sparsity = egraph[x].metadata.sparsity.unwrap();
            let y_sparsity = egraph[y].metadata.sparsity.unwrap();

            let sparsity = std::cmp::min(x_sparsity, y_sparsity);

            let vol: usize = schema.values().product();
            let nnz = NotNan::from(vol as f64) * sparsity;
            nnz.round() as usize
        },
        Math::Agg => {
            debug_assert_eq!(expr.children.len(), 2, "wrong length in agg");
            let i = expr.children[0];
            let body = expr.children[1];
            let body_schm = egraph[body].metadata.schema.as_ref().unwrap().get_schm();
            if body_schm.len() > 2 {
                10000000
            } else {
                let sparsity = egraph[body].metadata.sparsity.unwrap();
                let vol: usize = body_schm.values().product();
                let len = egraph[i].metadata.schema.as_ref().unwrap().get_dims().1;

                // sparsity * vol / (vol / len)
                let nnz = (NotNan::from(*len as f64) * sparsity).round() as usize;
                std::cmp::min(nnz, vol / len)
            }
        },
        _ => 0
    }
}

pub fn trans_cost(_egraph: &EGraph, expr: &Expr<Math, Id>) -> usize {
    use Math::*;
    match expr.op {
        LMat | LAdd | LMin | LMul |
        MMul | LTrs | Srow | Scol |
        Sall | Bind | Ubnd | LLit |
        Sub => 1,
        _ => 0
    }
}
