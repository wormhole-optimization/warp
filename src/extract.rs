use crate::{EGraph, Math, Schema};

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

pub fn extract(egraph: EGraph, roots: &[Id]) -> Vec<RecExpr<Math>> {
    let mut problem = LpProblem::new("wormhole", LpObjective::Minimize);

    // Create symbolic variables Bn (for each node) & Bq (each class)
    let mut var_bns = BiMap::<&Expr<Math, Id>, String>::new();
    let mut var_bqs = BiMap::<Id, String>::new();

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
                if let None = var_bqs.get_by_right(&var_name) {
                    panic!("solver selected nonexistent node")
                }
            }
        }
    }

    roots.iter().map(|root| find_expr(&egraph, *root, &selected)).collect()
}

fn find_expr(egraph: &EGraph, class: Id, selected: &HashSet<&Expr<Math, Id>>) -> RecExpr<Math> {
    let eclass = egraph.find(class);
    let best_node = egraph[eclass]
        .iter()
        .find(|n| selected.contains(n))
        .expect("no node selected in class");

    best_node
        .clone()
        .map_children(|child| find_expr(egraph, child, selected))
        .into()
}

fn cost(egraph: &EGraph, expr: &Expr<Math, Id>) -> usize {
    match expr.op {
        Math::Add => {
            assert_eq!(expr.children.len(), 2);
            let x = expr.children[0];
            let y = expr.children[1];

            let x_schema = egraph[x].metadata.schema.as_ref()
                .expect("wrong schema in argument to add");
            let y_schema = egraph[y].metadata.schema.as_ref()
                .expect("wrong schema in argument to add");
            let schema = Some(x_schema.union(&y_schema));

            let x_sparsity = egraph[x].metadata.sparsity;
            let y_sparsity = egraph[y].metadata.sparsity;

            let sparsity =
                if let (Some(x_s), Some(y_s)) = (x_sparsity, y_sparsity) {
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
            nnz.round() as usize
        },
        Math::Mul => {
            assert_eq!(expr.children.len(), 2);
            let x = expr.children[0];
            let y = expr.children[1];

            let x_schema = egraph[x].metadata.schema.as_ref()
                .expect("wrong schema in argument to mul");
            let y_schema = egraph[y].metadata.schema.as_ref()
                .expect("wrong schema in argument to mul");
            let schema = Some(x_schema.union(&y_schema));

            let x_sparsity = egraph[x].metadata.sparsity;
            let y_sparsity = egraph[y].metadata.sparsity;

            let sparsity =
                if let (Some(x_s), Some(y_s)) = (x_sparsity, y_sparsity) {
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
            nnz.round() as usize
        },
        Math::Agg => {
            assert_eq!(expr.children.len(), 2, "wrong length in agg");
            let i = expr.children[0];
            let body = expr.children[1];

            let sparsity = egraph[body].metadata.sparsity
                .expect("no sparsity in aggregate body");

            let len = if let Schema::Dims(k, v)
                = egraph[i].metadata.schema.as_ref().unwrap() {
                    v
                } else {
                    panic!("wrong dimension in aggregate")
                };

            (NotNan::from(*len as f64) * sparsity).round() as usize
        },
        _ => 0
    }
}
