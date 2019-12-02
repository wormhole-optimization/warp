use egg::{
    egraph::{EClass, EGraph},
    expr::{Expr, Id, Language, RecExpr},
};

use indexmap::IndexMap;
use std::cmp::Ordering;

pub type Cost = f64;

pub struct CostExpr<L: Language> {
    pub cost: Cost,
    pub expr: RecExpr<L>,
}

pub struct Extractor<'a, L: Language, M> {
    costs: IndexMap<Id, Cost>,
    egraph: &'a EGraph<L, M>,
    model: fn(&L, &[Cost]) -> Cost,
}

fn cmp(a: &Option<Cost>, b: &Option<Cost>) -> Ordering {
    // None is high
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(a), Some(b)) => a.partial_cmp(&b).unwrap(),
    }
}

impl<'a, L: Language, M> Extractor<'a, L, M> {
    pub fn new(egraph: &'a EGraph<L, M>,
               model: fn(&L, &[Cost]) -> Cost,
    ) -> Self {
        let costs = IndexMap::default();
        let mut extractor = Extractor { costs, egraph, model };
        extractor.find_costs();

        extractor
    }

    pub fn calculate_cost(&self, expr: &RecExpr<L>) -> Cost {
        let child_costs: Vec<_> =
            expr.as_ref().children.iter().map(|e| self.calculate_cost(e)).collect();
        (self.model)(&expr.as_ref().op, &child_costs)
    }

    pub fn find_best(&self, eclass: Id) -> CostExpr<L> {
        let expr = self.find_best_expr(eclass);
        let cost = self.calculate_cost(&expr);
        CostExpr { cost, expr }
    }

    fn find_best_expr(&self, eclass: Id) -> RecExpr<L> {
        let eclass = self.egraph.find(eclass);

        let best_node = self.egraph[eclass]
            .iter()
            .filter(|n| self.node_total_cost(n).is_some())
            .min_by(|a, b| {
                let a = self.node_total_cost(a);
                let b = self.node_total_cost(b);
                cmp(&a, &b)
            })
            .expect("eclass shouldn't be empty");

        best_node
            .clone()
            .map_children(|child| self.find_best_expr(child))
            .into()
    }

    fn node_total_cost(&self, node: &Expr<L, Id>) -> Option<Cost> {
        let child_costs: Option<Vec<_>> =
            node.children.iter().map(|id| self.costs.get(id).cloned()).collect();
        let cost = (self.model)(&node.op, &child_costs?);
        Some(cost)
    }

    fn find_costs(&mut self) {
        let mut did_something = true;
        while did_something {
            did_something = false;

            for class in self.egraph.classes() {
                match (self.costs.get(&class.id), self.make_pass(class)) {
                    (None, Some(cost)) => {
                        self.costs.insert(class.id, cost);
                        did_something = true;
                    }
                    (Some(old), Some(new)) if new < *old => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    _ => (),
                }
            }
        }
    }

    fn make_pass(&self, eclass: &EClass<L, M>) -> Option<Cost> {
        eclass.iter().map(|n| self.node_total_cost(n)).min_by(cmp).unwrap()
    }
}
