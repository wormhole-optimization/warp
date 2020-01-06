use warp::{Math, EGraph, rules, untrans_rules, trans_rules, extract, parse_hop, load_dag, optimize, print_dag, dag_cost};
use egg::{
    //define_term,
    //egraph::{AddResult, EClass, Metadata},
    //expr::{Expr, Language, QuestionMarkName},
    extract::{calculate_cost, Extractor},
    parse::ParsableLanguage,
    //pattern::{Applier, Rewrite, WildMap},
};
use log::*;

//use std::env;
use std::fs;
use std::env;

fn main() {
    let _ = env_logger::builder().is_test(false).try_init();
    let args: Vec<String> = env::args().collect();
    let hops = &args[1];
    let _ = env_logger::builder().is_test(true).try_init();
    let contents = fs::read_to_string(hops)
        .expect("Something went wrong reading the file");

    let mut egraph = EGraph::default();
    let root = load_dag(&mut egraph, &contents);
    let sol = optimize(egraph, root);

    for s in sol.iter() {
        let sol_s = s.pretty(80);
        //println!("{}", sol_s);
    }
    let mut egraph = EGraph::default();
    for s in sol.iter() {
        egraph.add_expr(&s);
    }
    print_dag(&egraph);
}
