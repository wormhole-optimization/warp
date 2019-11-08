use crate::{Math, EGraph, Expr};
use egg::parse::ParsableLanguage;
use std::collections::HashMap;

pub static HOP: &str = "29,29;80;LiteralOp 6.14;;0,0,-1,-1,-1;S;D;0,0,0,0;;;";

#[derive(Debug)]
pub struct Hop {
    id: u32,
    op: Math,
    children: Vec<u32>,
    row: u32,
    col: u32,
    nnz: Option<u32>,
}

fn ops() -> HashMap<&'static str, Math> {
    use Math::*;
    [("r(t)", LTrs),
     ("b(*)", LMul),
     ("b(+)", LAdd),
     ("ba(+*)", MMul),
     ("ua(+R)", Srow),
     ("ua(+C)", Scol),
     ("ua(+RC)", Sall),
    ].iter().cloned().collect()
}

fn get_lit(s: &str) -> Option<Math> {
    if s.starts_with("LiteralOp") {
        let n: i32 = s.split_whitespace().nth(1).unwrap().parse().unwrap();
        Some(Math::Num(n))
    } else {
        None
    }
}

fn get_var(s: &str) -> Option<Math> {
    if s.starts_with("TRead") {
        let v = s.split_whitespace().nth(1).unwrap();
        Some(Math::Str(v.to_owned()))
    } else {
        None
    }
}

pub fn parse_hop(s: &str) -> Hop {
    let hop: Vec<_> = s.split(";").collect();
    let id: u32 = hop[1].parse().unwrap();
    let op_s = hop[2];
    let op = ops().get(op_s).cloned()
        .or(get_var(op_s))
        .or(get_lit(op_s))
        .unwrap();
    let children: Vec<u32> = hop[3].split(",").filter_map(|s| s.parse().ok()).collect();

    let meta: Vec<Option<u32>> = hop[4].split(",").map(|s| s.parse().ok()).collect();
    let mut row = meta[0].unwrap_or(0);
    if row == 0 { row = 1 };
    let mut col = meta[1].unwrap_or(0);
    if col == 0 { col = 1 };
    let nnz = meta[4];

    Hop{id, op, children, row, col, nnz}
}

pub fn load_dag(egraph: &mut EGraph, s: &str) -> u32 {
    use Math::*;
    let mut id_map = HashMap::new();
    let hops = s.lines();
    let mut root = 0;
    for h in hops {
        let hop = parse_hop(h);
        // TODO special case for literal, string
        match hop.op {
            Num(n) => {
                let s = format!("(llit {})", n);
                let exp = Math::parse_expr(&s).unwrap();
                let lit = egraph.add_expr(&exp);
                id_map.insert(hop.id, lit);
                root = lit;
            },
            Str(x) => {
                let m = format!("(lmat {x} {i} {j} {z})", x=x, i=hop.row, j=hop.col, z=hop.nnz.unwrap());
                let exp = Math::parse_expr(&m).unwrap();
                let mat = egraph.add_expr(&exp);
                id_map.insert(hop.id, mat);
                root = mat;
            }
            op => {
                let children: Vec<_> = hop.children.iter().map(|c| id_map[c]).collect();
                let id = egraph.add(Expr::new(op, children.into())).id;
                id_map.insert(hop.id, id);
                root = id;
            }
        }
    }
    root
}
