use crate::{EGraph, Math, Schema, get_vol};

use egg::expr::{Expr, Id, RecExpr};

use lp_modeler::solvers::{GurobiSolver, SolverTrait};
use lp_modeler::dsl::*;

use bimap::BiMap;

use std::{
    collections::HashSet,
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};
use std::time::Instant;

pub fn extract(egraph: EGraph,
               roots: &[Id],)
               //cost: fn(&EGraph, &Expr<Math, Id>) -> usize)
               -> Vec<RecExpr<Math>>
{
    let mut problem = LpProblem::new("wormhole", LpObjective::Minimize);

    // Create symbolic variables Bn (for each node) & Bq (each class)
    let mut var_bns = BiMap::<&Expr<Math, Id>, String>::new();
    let mut var_bqs = BiMap::<Id, String>::new();
    //let mut var_bij = HashMap::<(String, String), String>::new();

    for c in egraph.classes() {
        // only pick if dimensions are good
        match &c.metadata.schema {
            Some(Schema::Schm(s)) if s.len() > 2 => {},
            _ => {
                let bq = "bq".to_owned() + &c.id.to_string();
                var_bqs.insert(c.id, bq);

                for e in c.nodes.iter() {
                    // generate variable only if e can be expressed in LA
                    match e.op {
                        Math::Add | Math::Mul if {
                            debug_assert_eq!(e.children.len(), 2);
                            let x_schema = egraph[e.children[0]]
                                .metadata.schema.as_ref().unwrap().get_schm().clone();
                            let y_schema = egraph[e.children[1]]
                                .metadata.schema.as_ref().unwrap().get_schm().clone();
                            x_schema.len() == 1 && y_schema.len() == 1 && x_schema != y_schema
                        }
                        => {
                            // row vec +/* col vec not allowed in LA
                        },
                        _ => {
                            let mut s = DefaultHasher::new();
                            e.hash(&mut s);
                            let bn = "bn".to_owned() + &s.finish().to_string();
                            var_bns
                                .insert_no_overwrite(e, bn)
                                .expect("equal exprs not merged");
                        }
                    }
                }
            }
        }
    };
     println!("DONE generating vars");

    // Objective function to minimize
    let obj_vec: Vec<LpExpression> = {
        var_bqs.iter().flat_map(|(c, var)| {
            let meta = &egraph[*c].metadata;
            if let Some(Schema::Schm(_)) = meta.schema {
                let coef = meta.nnz.unwrap_or(get_vol(meta));
                let bq = LpBinary::new(&var);
                Some(coef as f32 * &bq)
            } else {
                None
            }
        }).collect()
    };

    println!("so many vars {:?}", obj_vec.len());

    // for term in obj_vec {
    //     problem += term;
    // }
    problem += obj_vec.sum();
    println!("DONE adding objective");

    // Constraint Br: must pick roots

    for root in roots {
        let br = LpBinary::new(&var_bqs.get_by_left(&root).unwrap());
        problem += (0 + &br).equal(1);
    }

    // Constraints Gq & Fn
    // Gq: Bq => OR Bn in q.nodes
    // Fn: Bn => AND Bq in n.children
    for class in egraph.classes() {
        if let Some(bq_s) = &var_bqs.get_by_left(&class.id) {
            let bq = LpBinary::new(bq_s);
            // Gq <=> (1-Bq) + (sum Bn) > 0
            let bns: Vec<&String> = class.nodes.iter().filter_map(|n| {
                var_bns.get_by_left(&n)
            }).collect();
            if bns.is_empty() {
                problem += (0+bq).equal(0);
            } else {
                let sum_bn = sum(&bns, |n| LpBinary::new(&n));
                problem += (1 - bq + sum_bn).ge(1);
            }

            // Fn <=> AND_Bq . (1-Bn) + Bq > 0
            for node in class.iter() {
                if let Some(bn) = &var_bns.get_by_left(&node) {
                    let bn = LpBinary::new(bn);
                    for class in node.children.iter() {
                        if let Some(bq) = &var_bqs.get_by_left(&class) {
                            let bq = LpBinary::new(bq);
                            problem += ((1 - &bn) + bq).ge(1);
                        } else {
                            problem += (0 + &bn).equal(0)
                        }
                    }
                }
            }
        }
    }

    println!("START SOLVING");
    let start_time = Instant::now();
    let solver = GurobiSolver::new();
    let result = solver.run(&problem);
    let solve_time = start_time.elapsed();
    println!("SOLVE TIME {:?}", solve_time);
    println!("DONE SOLVING");

    let var_values = result.unwrap().results;

    // Lookup selected nodes and classes
    let mut selected = HashSet::new();
    let mut cost = 0;

    for (var_name, var_value) in &var_values {
        let int_var_value = *var_value as u32;
        if int_var_value == 1 {
            if let Some(&v) = var_bns.get_by_right(&var_name) {
                selected.insert(v);
            } else {
                if let Some(&v) = var_bqs.get_by_right(&var_name) {
                    let nnz = egraph[v].metadata.nnz.unwrap_or(0);
                    cost += nnz;
                }
            }
        }
    }
    println!("SELECTED COST {:?}", cost);
    roots.iter().map(|root| find_expr(&egraph, *root, &selected)).collect()
}

fn find_expr(egraph: &EGraph, class: Id, selected: &HashSet<&Expr<Math, Id>>) -> RecExpr<Math> {
    println!("CLASS {:?}", class);
    let eclass = egraph.find(class);
    for n in egraph[class].iter() {
      println!("NODE {:?}", n);
    }
    let best_node = egraph[eclass]
        .iter()
        .find(|n| selected.contains(n))
        .expect(&format!("no node selected in class {}", class));
    best_node
        .clone()
        .map_children(|child| find_expr(egraph, child, selected))
        .into()
}
