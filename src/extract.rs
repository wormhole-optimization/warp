use crate::{EGraph, Math, Schema, Sparsity};

use egg::{
    expr::{Expr, Id, RecExpr},
    //extract::{calculate_cost, Extractor},
};
use lp_modeler::solvers::{GurobiSolver, SolverTrait};
use lp_modeler::dsl::*;
use bimap::BiMap;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;
use ordered_float::NotNan;

pub fn extract(egraph: EGraph, root: Id) {
    let mut problem = LpProblem::new("wormhole", LpObjective::Minimize);

    let mut var_bns = BiMap::<&Expr<Math, Id>, SymVar>::new();
    let mut var_bqs = BiMap::<Id, SymVar>::new();

    let mut cs = HashSet::new();

    for c in egraph.classes() {
        cs.insert(c.id);
        for e in c.nodes.iter() {
            for class in e.children.iter() {
                cs.insert(*class);
            }
        }
    }

    let mut count = 0;

    for _ in egraph.classes() {
        count += 1;
    }

    let clen = cs.len();

    assert_eq!(count, clen, "DIFFERS BY {}", clen - count);

    for c in egraph.classes() {
        let bqv = "bq".to_owned() + &c.id.to_string();
        let bq = LpBinary::new(&bqv);
        var_bqs.insert(c.id, SymVar(bq));

        for e in c.nodes.iter() {
            let mut s = DefaultHasher::new();
            e.hash(&mut s);
            let bnv = "bn".to_owned() + &s.finish().to_string();
            let bn = LpBinary::new(&bnv);
            var_bns.insert_no_overwrite(e, SymVar(bn)).expect("equal exprs not merged");
        }
    };

    let obj_vec: Vec<LpExpression> = {
        var_bns.iter().map(|(e, bin)| {
            let coef = cost(&egraph, e);
            coef as f32 * &bin.0
        }).collect()
    };

    println!("after cost");
    println!("{:?}", obj_vec.len());

    problem += obj_vec.sum();

    println!("after cost");

    // Br: must pick root
    problem += (0 + &var_bqs.get_by_left(&root).unwrap().0).equal(1);

    println!("before gq");

    for class in egraph.classes() {
        // Gq: Bq => OR Bn in q.nodes
        // (not Bq) or (OR Bn)
        // (1-Bq) + (sum Bn) > 0
        problem += ((1-&var_bqs.get_by_left(&class.id).unwrap().0) + sum(&class.nodes, |n| &var_bns.get_by_left(&n).unwrap().0)).ge(1);

        for node in class.iter() {
            // Fn: Bn => AND Bq in n.children
            // (not Bn) or (AND Bq)
            let bn = &var_bns.get_by_left(&node).unwrap().0;
            for class in node.children.iter() {
                // (1-Bn) + bq > 0
                let bq = &var_bqs.get_by_left(&class).unwrap().0;
                problem += ((1-bn) + bq).ge(1);
            }
        }
    }

    println!("after gq");

    let solver = GurobiSolver::new();
    let result = solver.run(&problem);

    println!("{:?}", result);
    assert!(result.is_ok(), result.unwrap_err());

    let (_solver_status, var_values) = result.unwrap();

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

#[derive(PartialEq, Debug)]
struct SymVar(LpBinary);

impl Eq for SymVar {}

impl Hash for SymVar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.name.hash(state);
    }
}

fn cost(egraph: &EGraph, expr: &Expr<Math, Id>) -> usize {
    match expr.op {
        Math::Add => {
            assert_eq!(expr.children.len(), 2);
            let x = expr.children[0];
            let y = expr.children[1];

            egraph[x].metadata.nnz + egraph[y].metadata.nnz
        },
        Math::Mul => {
            assert_eq!(expr.children.len(), 2, "wrong length in mul");
            let x_id = &expr.children[0];
            let x = &egraph[*x_id].metadata;
            let y_id = &expr.children[1];
            let y = &egraph[*y_id].metadata;

            let schema = x. schema.union(&y.schema);

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
            nnz.round() as usize
        },
        Math::Agg => {
            assert_eq!(expr.children.len(), 2, "wrong length in mul");
            let i_id = &expr.children[0];
            let i = &egraph[*i_id].metadata;
            let body_id = &expr.children[1];
            let body = &egraph[*body_id].metadata;

            if let Schema::Dims(_, size) = i.schema {
                match body.sparsity {
                    Sparsity::Sparse(s) => (NotNan::from(size as f64) * s).round() as usize,
                    _ => size
                }
            } else {
                panic!("wrong schema in dimension")
            }

        },
        _ => 0
    }
}
