use crate::{EGraph, Math, Schema, Sparsity};

use egg::expr::{Expr, Id, RecExpr};

use lp_modeler::solvers::{GurobiSolver, SolverTrait};
use lp_modeler::dsl::*;

use bimap::BiMap;
use ordered_float::NotNan;

use std::{
    collections::HashSet,
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

pub fn extract(egraph: EGraph, root: Id) -> RecExpr<Math> {
    let mut problem = LpProblem::new("wormhole", LpObjective::Minimize);

    // Create symbolic variables Bn (for each node) & Bq (each class)
    let mut var_bns = BiMap::<&Expr<Math, Id>, SymVar>::new();
    let mut var_bqs = BiMap::<Id, SymVar>::new();

    for c in egraph.classes() {
        let bq = "bq".to_owned() + &c.id.to_string();
        var_bqs.insert(c.id, SymVar::new(&bq));

        for e in c.nodes.iter() {
            let mut s = DefaultHasher::new();
            e.hash(&mut s);
            let bn = "bn".to_owned() + &s.finish().to_string();

            var_bns
                .insert_no_overwrite(e, SymVar::new(&bn))
                .expect("equal exprs not merged");
        }
    };

    // Objective function to minimize
    let obj_vec: Vec<LpExpression> = {
        var_bns.iter().map(|(e, bin)| {
            let coef = cost(&egraph, e);
            coef as f32 * &bin.0
        }).collect()
    };

    problem += obj_vec.sum();

    // Constraint Br: must pick root
    problem += (0 + &var_bqs.get_by_left(&root).unwrap().0).equal(1);

    // Constraints Gq & Fn
    // Gq: Bq => OR Bn in q.nodes
    // Fn: Bn => AND Bq in n.children
    for class in egraph.classes() {
        // Gq <=> (1-Bq) + (sum Bn) > 0
        let bq = &var_bqs.get_by_left(&class.id).unwrap().0;
        let sum_bn = sum(&class.nodes, |n| {
            let bn = &var_bns.get_by_left(&n).unwrap().0;
            bn
        });
        problem += (1 - bq + sum_bn).ge(1);

        // Fn <=> AND_Bq . (1-Bn) + Bq > 0
        for node in class.iter() {
            let bn = &var_bns.get_by_left(&node).unwrap().0;
            for class in node.children.iter() {
                let bq = &var_bqs.get_by_left(&class).unwrap().0;
                problem += ((1 - bn) + bq).ge(1);
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
            if let Some(&v) = var_bns.get_by_right(&SymVar::new(var_name)) {
                selected.insert(v);
            } else {
                panic!("solver selected nonexistent node")
            }
        }
    }

    find_expr(&egraph, root, &selected)
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

#[derive(PartialEq, Debug)]
struct SymVar(LpBinary);

impl Eq for SymVar {}

impl Hash for SymVar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.name.hash(state);
    }
}

impl SymVar {
    fn new(s: &str) -> Self {
        SymVar(LpBinary::new(s))
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
