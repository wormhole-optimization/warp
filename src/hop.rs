use crate::{Math, EGraph, Expr};
use egg::parse::ParsableLanguage;
use std::collections::HashMap;
use smallvec::smallvec;

pub static HOP: &str = "29,29;80;LiteralOp 6.14;;0,0,-1,-1,-1;S;D;0,0,0,0;;;";

#[derive(Debug)]
pub struct Hop {
    id: u32,
    op: Math,
    children: Vec<u32>,
    row: u32,
    col: u32,
    nnz: Option<i32>,
}

fn op(s: &str) -> Option<Math> {
    use Math::*;
    match s {
        "r(t)" => Some(LTrs),
        "b(*)" => Some(LMul),
        "b(+)" => Some(LAdd),
        "b(-)" => Some(LMin),
        "ba(+*)" => Some(MMul),
        "ua(+R)" => Some(Srow),
        "ua(+C)" => Some(Scol),
        "ua(+RC)" => Some(Sall),
        _ => None,
    }
}

fn get_lit(s: &str) -> Option<Math> {
    if s.starts_with("LiteralOp") {
        let n: f64 = s.split_whitespace().nth(1).unwrap().parse().unwrap();
        Some(Math::Num(n.into()))
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

fn get_write(s: &str) -> Option<Math> {
    if s.starts_with("TWrite") {
        let v = s.split_whitespace().nth(1).unwrap();
        Some(Math::TWrite(v.to_owned()))
    } else {
        None
    }
}

fn get_udf(s: &str) -> Option<Math> {
    Some(Math::Str(s.to_owned()))
}

pub fn parse_hop(s: &str) -> Hop {
    let hop: Vec<_> = s.split(";").collect();
    let id: u32 = hop[1].parse().unwrap();
    let op_s = hop[2];
    let op = op(op_s)
        .or(get_write(op_s))
        .or(get_var(op_s))
        .or(get_lit(op_s))
        .or(get_udf(op_s))
        .unwrap();
    let children: Vec<u32> = hop[3].split(",").filter_map(|s| s.parse().ok()).collect();

    let meta: Vec<Option<i32>> = hop[4].split(",").map(|s| s.parse().ok()).collect();
    let mut row = meta[0].unwrap_or(0);
    if row == 0 || row == -1 { row = 1 };
    let mut col = meta[1].unwrap_or(0);
    if col == 0 || col == -1 { col = 1 };
    let mut nnz = meta[4];
    if let Some(-1) = nnz {
        nnz = Some(row as i32 * col as i32)
    }

    Hop{id, op, children, row : row as u32, col : col as u32, nnz}
}

pub fn load_dag(egraph: &mut EGraph, s: &str) -> Vec<u32> {
    use Math::*;
    let mut id_map = HashMap::new();
    let hops = s.lines();
    let mut roots = vec![];
    for h in hops {
        let hop = parse_hop(h);
        // TODO special case for literal, string
        match hop.op {
            Num(n) => {
                let s = format!("(llit {})", n);
                let exp = Math::parse_expr(&s).unwrap();
                let lit = egraph.add_expr(&exp);
                id_map.insert(hop.id, lit);
            },
            Str(x) => {
                let mut args = hop.children;
                if args.is_empty() {
                    let m = format!("(lmat {x} {i} {j} {z})", x=x, i=hop.row, j=hop.col, z=hop.nnz.unwrap());
                    let exp = Math::parse_expr(&m).unwrap();
                    let mat = egraph.add_expr(&exp);
                    id_map.insert(hop.id, mat);
                } else {
                    // add dimensions to children for rix / lix (right and left index)
                    if x == "rix" || x == "lix" {
                        let row = egraph.add(Expr::new(Math::Num((hop.row as f64).into()), smallvec![]));
                        let col = egraph.add(Expr::new(Math::Num((hop.col as f64).into()), smallvec![]));
                        args.push(row.id);
                        args.push(col.id);
                        id_map.insert(row.id, row.id);
                        id_map.insert(col.id, col.id);
                    }
                    let op_s = egraph.add(Expr::new(Str(x), smallvec![]));
                    let mut children  = smallvec![op_s.id];
                    children.extend(args.iter().map(|c| id_map[c]));
                    let udf = egraph.add(Expr::new(Udf, children)).id;
                    id_map.insert(hop.id, udf);
                }
            },
            op => {
                let children: Vec<_> = hop.children.iter().map(|c| id_map[c]).collect();
                let id = egraph.add(Expr::new(op.clone(), children.into())).id;
                if let TWrite(_) = op {
                    roots.push(id);
                }
                id_map.insert(hop.id, id);
            }
        }
    }
    roots
}

pub fn print_dag(egraph: &EGraph) {
    use Math::*;
    for c in egraph.classes() {
        let id = &c.id;
        for e in &c.nodes {
            let op = &e.op;
            match op {
                Str(_) | Num(_) => {},
                Udf => {
                    print!("0,0;{id};", id=id);
                    let f = e.children[0];
                    let op = format!("{}", &egraph[f].nodes[0].op);
                    print!("{};", op);
                    //for e in &egraph[f].nodes {
                    //    print!("{};", e.op);
                    //}
                    let args = if op == "rix" || op == "lix" {
                        &e.children[1..6]
                    } else {
                        &e.children[1..]
                    };
                    for c in args {
                        print!("{},",c);
                    }
                    println!(";;M;D;;;;;")
                },
                LMat => {
                    print!("0,0;{id};TRead ", id=id);
                    let x = e.children[0];
                    for e in &egraph[x].nodes {
                        print!("{}", e.op);
                    }
                    println!(";;;M;D;;;;;")
                },
                LLit => {
                    print!("0,0;{id};LiteralOp ", id=id);
                    for c in &e.children {
                        for e in &egraph[*c].nodes {
                            print!("{}", e.op);
                        }
                    }
                    println!(";;;M;D;;;;;");
                },
                TWrite(s) => {
                    print!("0,0;{id};TWrite {var};", id=id, var=s);
                    for c in &e.children {
                        print!("{},",c);
                    }
                    println!(";;M;D;;;;;")
                },
                Var => {
                    println!("var");
                },
                op => {
                    print!("0,0;{id};{op};", id = id, op=dml_op(op));
                    for c in &e.children {
                        print!("{},",c);
                    }
                    println!(";;M;D;;;;;");
                }
            }
        }
    }
}

fn dml_op(op: &Math) -> &'static str {
    use Math::*;
    match op {
        LAdd => "b(+)",
        LMin => "b(-)",
        LMul => "b(*)",
        MMul => "ba(+*)",
        LTrs => "r(t)",
        Srow => "ua(+R)",
        Scol => "ua(+C)",
        Sall => "ua(+RC)",
        o => panic!("unknown op {:?}", o)
    }
}

// 29,29;86;TRead B;;500000,10,1000,1000,5000000;M;D;0,0,38,-;;;

// 29,29;80;LiteralOp 6.14;;0,0,-1,-1,-1;S;D;0,0,0,0;;;
// LMat = "lmat", LLit = "llit", Udf = "udf", Var = "var"
