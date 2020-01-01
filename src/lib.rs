use egg::{
    define_term,
    egraph::EClass,
    expr::{Expr, RecExpr, Language},
    pattern::Rewrite,
};

use std::collections::{HashSet, HashMap};
use std::hash::Hash;
use std::cmp::min;
use std::iter::*;

use ordered_float::NotNan;

mod translate;
pub use translate::Extractor;

mod hop;
pub use hop::*;

mod rules;
pub use rules::{rules, trans_rules, untrans_rules};

mod extract;
pub use extract::*;

pub type EGraph = egg::egraph::EGraph<Math, Meta>;

type Number = NotNan<f64>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    schema:   Option<Schema>,
    sparsity: Option<NotNan<f64>>,
    nnz:      Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Schema {
    Schm(HashMap<String, usize>),
    Dims(String, usize),
    Name(String),
    Size(usize),
    Mat(usize, usize),
}

pub fn dag_cost(eg: &EGraph) -> usize {
    eg.classes().map(|c| {
        let nnz = c.metadata.nnz;
        //if let None = nnz {
        //    println!("missing nnz for {:?}", c.metadata);
        //    for node in &c.nodes {
        //        println!("{:?}", node);
        //    }
        //}
        // println!("NNZ {:?}", nnz);
        nnz.unwrap_or(get_vol(&c.metadata))
    }).sum()
}

fn saturate(egraph: &mut EGraph, rws: &[Rewrite<Math, Meta>], iters: usize) {
    for _i in 1..iters {
        for rw in rws {
            rw.run(egraph);
        }
        egraph.rebuild();
    }
}

pub fn udf_meta(op: &str, children: &[&Meta]) -> Meta {
    match op {
        "b(/)" => {
            let x = &children[0];
            let x_schema = &children[0].schema.as_ref().unwrap();
            let y = &children[1];
            let y_schema = &children[1].schema.as_ref().unwrap();

            let (x_i, x_j) = x_schema.get_mat();
            let (y_i, y_j) = y_schema.get_mat();
            dims_ok(*x_i, *x_j, *y_i, *y_j);
            let row = if *x_i == 1 { y_i } else { x_i };
            let col = if *x_j == 1 { y_j } else { x_j };

            let sparsity = min(x.sparsity, y.sparsity);

            let nnz = sparsity.map(|sp| {
                let vol: usize = *row * *col;
                let nnz = NotNan::from(vol as f64) * sp;
                nnz.round() as usize
            });

            Meta {
                schema: Some(Schema::Mat(*row, *col)),
                nnz,
                sparsity
            }
        },
        "rix" => {
            // NOTE might want to tweak the nnz here
            let x = &children[0];
            let r = &children[5].schema.as_ref().unwrap();
            let row = r.get_size();
            let c = &children[6].schema.as_ref().unwrap();
            let col = c.get_size();
            Meta {
                schema: Some(Schema::Mat(*row, *col)),
                nnz: x.nnz,
                sparsity: x.sparsity,
            }
        },
        "lix" => {
            // NOTE might want to tweak the nnz here
            let x = &children[0];
            let r = &children[6].schema.as_ref().unwrap();
            let row = r.get_size();
            let c = &children[7].schema.as_ref().unwrap();
            let col = c.get_size();
            Meta {
                schema: Some(Schema::Mat(*row, *col)),
                nnz: x.nnz,
                sparsity: x.sparsity,
            }
        },
        "r(diag)" => {
            let x = &children[0];
            let x_schema = &children[0].schema.as_ref().unwrap();
            let (x_i, x_j) = x_schema.get_mat();

            let vol: Number = ((x_i * x_i * x_j * x_j) as f64).into();

            Meta {
                schema: Some(Schema::Mat(x_i * x_j, x_i * x_j)),
                nnz: x.nnz,
                sparsity: x.sparsity.map(|sp| sp / vol),
            }
        },
        "u(ncol)" | "u(nrow)" => {
            Meta {
                schema: Some(Schema::Mat(1, 1)),
                nnz: Some(1),
                sparsity: Some(1.0.into())
            }
        },
        "ua(minR)" => {
            let x = &children[0];
            let x_schema = &children[0].schema.as_ref().unwrap();
            let (x_i, _x_j) = x_schema.get_mat();
            let sparsity = x.sparsity;
            let nnz = sparsity.map(|s| s.round() as usize * x_i);

            Meta {
                schema: Some(Schema::Mat(*x_i, 1)),
                nnz,
                sparsity
            }
        },
        // NOTE nnz here can be wrong
        "b(^)" | "b(min)" | "b(&)" | "u(sqrt)" | "b(!=)" | "b(==)" | "b(>)" | "b(>=)" | "b(<)" | "b(<=)" | "u(exp)" | "u(log)" => {
            children[0].clone()
        },
        _ => panic!("Unknown udf {}", op)
    }
}

pub fn optimize(lgraph: EGraph, roots: Vec<u32>) -> Vec<RecExpr<Math>> {

    // Translate LA plan to RA
    println!("Translate LA plan to RA");
    let (mut trans_graph, roots) = (lgraph, roots);
    saturate(&mut trans_graph, &trans_rules(), 20);
    let trans_ext = Extractor::new(&trans_graph, trans_model);
    let rplans: Vec<_> = roots.iter().map(|r| trans_ext.find_best(*r).expr).collect();
    for rp in rplans.iter() {
        println!("{}", rp.pretty(80));
    }
    // Optimize RA plan
    println!("Optimize RA plan");
    let mut opt_graph = EGraph::default();
    let opt_roots: Vec<_> = rplans.iter().map(|rp| opt_graph.add_expr(rp)).collect();
    let orig_cost = dag_cost(&opt_graph);
    //println!("ROOT {:?}", opt_roots);
    saturate(&mut opt_graph, &rules(), 27);
    let best = extract(opt_graph, &opt_roots);
    for e in best.iter() {
        //println!("{}", e.pretty(80));
    }
    // Translate RA plan to LA
    println!("Translate RA plan to LA");
    let mut untrans_graph = EGraph::default();
    let untrans_roots: Vec<_> = best.iter().map(|p| untrans_graph.add_expr(p)).collect();
    let final_cost = dag_cost(&untrans_graph);
    saturate(&mut untrans_graph, &untrans_rules(), 50);
    let ext = Extractor::new(&untrans_graph, <Math as Language>::cost);
    let bests = untrans_roots.iter().map(|r| ext.find_best(*r).expr).collect();
    println!("COST BEFORE {}", orig_cost);
    println!("COST AFTER {}", final_cost);
    println!("SPEEDUP {}", final_cost as f64 / orig_cost as f64);
    bests
}

impl Schema {
    pub fn get_schm(&self) -> &HashMap<String, usize> {
        if let Self::Schm(s) = self {
            s
        } else {
            panic!("cannot get schm")
        }
    }

    pub fn get_dims(&self) -> (&String, &usize) {
        if let Self::Dims(i, n) = self {
            (i, n)
        } else {
            panic!("cannot get dims")
        }
    }

    pub fn get_name(&self) -> &String {
        if let Self::Name(n) = self {
            n
        } else {
            panic!("cannot get name")
        }
    }

    pub fn get_size(&self) -> &usize {
        if let Self::Size(s) = self {
            s
        } else {
            panic!("cannot get size")
        }
    }

    pub fn get_mat(&self) -> (&usize, &usize) {
        if let Self::Mat(i, j) = self {
            (i, j)
        } else {
            panic!("cannot get mat")
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        if let (Self::Schm(s1), Self::Schm(s2)) = (self, other) {
            let mut res = s1.clone();
            res.extend(s2.clone());
            Self::Schm(res)
        } else {
            panic!("unioning a non-schema")
        }
    }
}

impl egg::egraph::Metadata<Math> for Meta {
    type Error = std::convert::Infallible;

    fn modify(_eclass: &mut EClass<Math, Self>) {}
    fn merge(&self, other: &Self) -> Self {
        let sparsity = [self.sparsity, other.sparsity]
            .into_iter().flatten().min().copied();
        let nnz = [self.nnz, other.nnz]
            .into_iter().flatten().min().copied();
        debug_assert_eq!(&self.schema, &other.schema);
        let schema = self.schema.clone();
        // NOTE perhaps move the special case for 0 to
        // make(Mul)?
        // match (&sparsity, &nnz)  {
        //    (Some(f), Some(0)) if *f == 0.0.into() => {
        //            Some(Schema::Schm(HashMap::new()))
        //    },
        //    _ => {
        //        debug_assert_eq!(&self.schema, &other.schema);
        //        self.schema.clone()
        //    }
        //};
        Meta {schema, sparsity, nnz}
    }

    fn make(expr: Expr<Math, &Self>) -> Self {
        use Math::*;
        let schema = match expr.op {
            Add => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in add");
                let x = &expr.children[0];
                let y = &expr.children[1];

                let mut schema = x.schema.as_ref().unwrap().get_schm().clone();
                let y_schema = y.schema.as_ref().unwrap().get_schm().clone();
                schema.extend(y_schema);

                let sparsity = x.sparsity.and_then(|x| y.sparsity.map(|y| {
                        min(1.0.into(), x + y)
                }));

                let nnz = sparsity.map(|sp| {
                    let vol: usize = schema.values().product();
                    let nnz = NotNan::from(vol as f64) * sp;
                    nnz.round() as usize
                });

                let schema = Some(Schema::Schm(schema));

                Meta {schema, sparsity, nnz}
            },
            Mul => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in mul");
                let x = &expr.children[0];
                let y = &expr.children[1];

                let mut schema = x.schema.as_ref().unwrap().get_schm().clone();
                let y_schema = y.schema.as_ref().unwrap().get_schm().clone();
                schema.extend(y_schema);

                let sparsity = min(x.sparsity, y.sparsity);

                let nnz = sparsity.map(|sp| {
                    let vol: usize = schema.values().product();
                    let nnz = NotNan::from(vol as f64) * sp;
                    nnz.round() as usize
                });

                let schema = Some(Schema::Schm(schema));

                Meta {schema, sparsity, nnz}
            },
            Agg => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in sum");
                let body = &expr.children[1];

                let k = expr_schema(&expr, 0).get_dims().0;
                let mut body_schema = body.schema.as_ref().unwrap().get_schm().clone();
                body_schema.remove(k);

                let vol = body_schema.values().product();
                let sparsity = body.nnz.map(|nnz| { min(
                    1.0.into(),
                    NotNan::from(nnz as f64 / vol as f64)
                )});
                let nnz = body.nnz.map(|z| min(vol, z));

                let schema = Some(Schema::Schm(body_schema));

                Meta {schema, sparsity, nnz}
            },
            RMMul => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in rmmul");
                let x = &expr.children[0];
                let y = &expr.children[1];

                let mut x_schema = x.schema.as_ref().unwrap().get_schm().clone();
                let x_keys: HashSet<_> = x_schema.keys().cloned().collect();
                let y_schema = y.schema.as_ref().unwrap().get_schm().clone();
                let y_keys: HashSet<_> = y_schema.keys().cloned().collect();

                let j = x_keys.intersection(&y_keys).next().unwrap();

                x_schema.extend(y_schema);
                x_schema.remove(j);

                let vol: usize = x_schema.values().product();
                let sparsity = Some(1.0.into());
                let nnz = Some(vol);

                let schema = Some(Schema::Schm(x_schema));

                Meta {schema, sparsity, nnz}
            }
            Lit => {
                let num = &expr.children[0];
                Meta {
                    schema: Some(Schema::Schm(HashMap::default())),
                    sparsity: num.sparsity,
                    nnz: num.nnz
                }
            },
            Mat => {
                debug_assert_eq!(expr.children.len(), 4, "wrong length in matrix");
                let (i, n) = expr_schema(&expr, 1).get_dims();
                let (j, m) = expr_schema(&expr, 2).get_dims();

                let mut schema = HashMap::new();
                if *n != 1 {
                    schema.insert(i.clone(), *n);
                }
                if *m != 1 {
                    schema.insert(j.clone(), *m);
                };

                let nnz = expr.children[3].nnz;

                Meta {
                    schema: Some(Schema::Schm(schema)),
                    nnz,
                    sparsity: Some(NotNan::from(nnz.unwrap() as f64 / (n * m) as f64))
                }
            },
            Dim => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in dim");
                let schema = Schema::Dims(
                    expr_schema(&expr, 0).get_name().clone(),
                    *expr_schema(&expr, 1).get_size(),
                );
                Meta {
                    schema: Some(schema),
                    nnz: None,
                    sparsity: None
                }
            },
            Sub => {
                debug_assert_eq!(expr.children.len(), 3, "wrong length in subst");
                let (e_i, e_n) = expr_schema(&expr, 0).get_dims();
                let (v_i, v_n) = expr_schema(&expr, 1).get_dims();
                debug_assert_eq!(e_n, v_n, "substituting for different size");
                let body = &expr.children[2];

                let schema = match &body.schema.as_ref().unwrap() {
                    Schema::Schm(schema) => {
                        let mut res = schema.clone();
                        if let Some(m) = res.remove(v_i) {
                            res.insert(e_i.clone(), m);
                        }
                        Schema::Schm(res)
                    },
                    Schema::Dims(body_i, body_n) => {
                        if body_i == v_i {
                            Schema::Dims(e_i.clone(), *e_n)
                        } else {
                            Schema::Dims(body_i.clone(), *body_n)
                        }
                    },
                    Schema::Size(n) => panic!("cannot subst for size {:?}", n),
                    _ => panic!("cannot subst for attr. and mat")
                };

                Meta {
                    schema: Some(schema),
                    nnz: body.nnz,
                    sparsity: body.sparsity
                }
            },
            Var => {
                Meta {
                    schema: Some(Schema::Schm(HashMap::default())),
                    nnz: Some(1),
                    sparsity: Some(1.0.into())
                }
            },
            Num(n) => {
                Meta {
                    schema: Some(Schema::Size(n.into_inner().round() as usize)),
                    nnz: Some(if n == 0.0.into() { 0 } else { 1 }),
                    sparsity: Some(if n == 0.0.into() {0.0.into()} else {1.0.into()})
                }
            },
            Nnz => {
                let n = expr_schema(&expr, 0).get_size();
                Meta {
                    schema: None,
                    nnz: Some(*n),
                    sparsity: None,
                }
            },
            Str(s) => {
                Meta {
                    schema: Some(Schema::Name(s)),
                    nnz: Some(1),
                    sparsity: Some(1.0.into())
                }
            },
            // Schema rules for LA plans
            Udf => {
                let op_s = expr_schema(&expr, 0).get_name();
                let args = &expr.children[1..];
                udf_meta(op_s, args)
            },
            LMat => {
                debug_assert_eq!(expr.children.len(), 4, "wrong length in lmat");
                let row = expr_schema(&expr, 1).get_size();
                let col = expr_schema(&expr, 2).get_size();
                let nnz = &expr.children[3].nnz;
                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: *nnz,
                    sparsity: None
                }
            },
            LMin => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in lmin");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                let (y_i, y_j) = expr_schema(&expr, 1).get_mat();
                dims_ok(*x_i, *x_j, *y_i, *y_j);
                let row = if *x_i == 1 { y_i } else { x_i };
                let col = if *x_j == 1 { y_j } else { x_j };
                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: None,
                    sparsity: None
                }
            },
            LAdd => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in ladd");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                let (y_i, y_j) = expr_schema(&expr, 1).get_mat();
                dims_ok(*x_i, *x_j, *y_i, *y_j);
                let row = if *x_i == 1 { y_i } else { x_i };
                let col = if *x_j == 1 { y_j } else { x_j };
                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: None,
                    sparsity: None
                }
            },
            LMul => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in lmul");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                let (y_i, y_j) = expr_schema(&expr, 1).get_mat();
                dims_ok(*x_i, *x_j, *y_i, *y_j);
                let row = if *x_i == 1 { y_i } else { x_i };
                let col = if *x_j == 1 { y_j } else { x_j };
                Meta {
                    schema: Some(Schema::Mat(*row, *col)),
                    nnz: None,
                    sparsity: None
                }
            },
            MMul => {
                debug_assert_eq!(expr.children.len(), 2, "wrong length in mmul");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                let (y_i, y_j) = expr_schema(&expr, 1).get_mat();
                debug_assert_eq!(*x_j, *y_i, "wrong dimensions in mmul");
                Meta {
                    schema: Some(Schema::Mat(*x_i, *y_j)),
                    nnz: None,
                    sparsity: None
                }
            },
            LTrs => {
                debug_assert_eq!(expr.children.len(), 1, "wrong length in transpose");
                let (x_i, x_j) = expr_schema(&expr, 0).get_mat();
                Meta {
                    schema: Some(Schema::Mat(*x_j , *x_i)),
                    nnz: None,
                    sparsity: None
                }
            },
            Srow => {
                debug_assert_eq!(expr.children.len(), 1, "wrong length in transpose");
                let x_i = expr_schema(&expr, 0).get_mat().0;
                Meta {
                    schema: Some(Schema::Mat(*x_i , 1)),
                    nnz: None,
                    sparsity: None
                }
            },
            Scol => {
                debug_assert_eq!(expr.children.len(), 1, "wrong length in transpose");
                let x_j = expr_schema(&expr, 0).get_mat().1;
                Meta {
                    schema: Some(Schema::Mat(1, *x_j)),
                    nnz: None,
                    sparsity: None
                }
            },
            Sall => {
                Meta {
                    schema: Some(Schema::Mat(1, 1)),
                    nnz: None,
                    sparsity: None
                }
            },
            Bind => {
                debug_assert_eq!(expr.children.len(), 3, "wrong length in lmat");
                let i = expr_schema(&expr, 0).get_name();
                let j = expr_schema(&expr, 1).get_name();
                let x = &expr.children[2];
                let (x_row, x_col) = expr_schema(&expr, 2).get_mat();
                let mut schema = HashMap::new();
                if *x_row != 1 {
                    schema.insert(i.clone(), *x_row);
                }
                if *x_col != 1 {
                    schema.insert(j.clone(), *x_col);
                }
                Meta {
                    schema: Some(Schema::Schm(schema)),
                    nnz: x.nnz,
                    sparsity: x.sparsity
                }
            },
            Ubnd => {
                debug_assert_eq!(expr.children.len(), 3, "wrong length in ubind");
                let i = expr_schema(&expr, 0).get_name();
                let j = expr_schema(&expr, 1).get_name();
                let x = &expr.children[2];
                let x_schm = expr_schema(&expr, 2).get_schm();
                let row = *x_schm.get(i).unwrap_or(&1);
                let col = *x_schm.get(j).unwrap_or(&1);
                Meta {
                    schema: Some(Schema::Mat(row, col)),
                    nnz: x.nnz,
                    sparsity: x.sparsity
                }
            },
            LLit => {
                debug_assert_eq!(expr.children.len(), 1, "wrong length in lmat");
                Meta {
                    schema: Some(Schema::Mat(1, 1)),
                    nnz: None,
                    sparsity: None
                }
            },
            TWrite(_) => Meta {
                schema: None,
                nnz: None,
                sparsity: None,
            },
        };
        schema
    }
}

fn expr_schema<'a>(expr: &Expr<Math, &'a Meta>, i: usize) -> &'a Schema {
    expr.children[i].schema.as_ref().unwrap()
}

fn dims_ok(x_i: usize, x_j: usize, y_i: usize, y_j: usize) {
    debug_assert!(
        (x_i == y_i && x_j == y_j)
            || (x_i == y_i && y_j == 1)
            || (x_i == y_i && x_j == 1)
            || (x_i == 1 && x_j == y_j)
            || (y_i == 1 && x_j == y_j)
            || (x_i == 1 && x_j == 1)
            || (y_i == 1 && y_j == 1),
        format!("{:?}", (x_i, x_j, y_i, y_j))
    );
}

define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub enum Math {
        // LA
        LMat = "lmat", LAdd = "l+", LMin = "l-",
        LMul = "l*", MMul = "m*", LTrs = "trans",
        Srow = "srow", Scol = "scol", Sall = "sall",
        Bind = "b+", Ubnd = "b-", LLit = "llit",
        Udf = "udf",
        // RA
        Add = "+", Mul = "*", Agg = "sum", RMMul = "rm*",
        Lit = "lit", Var = "var", Mat = "mat",
        Dim = "dim", Nnz = "nnz", Sub = "subst",
        Num(Number), Str(String),
        // NOTE careful here, TWrite might be parsed as Str
        TWrite(String),
    }
}

// Cost to translate to LA
// TODO twrite?
impl Language for Math {
    fn cost(&self, children: &[f64]) -> f64 {
        use Math::*;
        let cost = match self {
            LMat | LAdd | LMin | LMul |
            MMul | LTrs | Srow | Scol |
            Sall | LLit | Udf |
            Num(_) | Str(_)=> 1.0,
            _ => 100.0
        };
        cost + children.iter().sum::<f64>()
    }
}

// Cost to translation to RA
// TODO twrite?
fn trans_model(op: &Math, children: &[f64]) -> f64 {
    use Math::*;
    let cost = match op {
        LMat | LAdd | LMin | LMul |
        MMul | LTrs | Srow | Scol |
        Sall | LLit |
        Sub => 100.0,
        Bind | Ubnd => 10.0,
        _ => 1.0
    };
    let c_cost: f64 = children.iter().sum();
    cost + c_cost
}

pub fn get_vol(m: &Meta) -> usize {
    if let Some(schm) = &m.schema {
        match schm {
            Schema::Schm(s) => s.values().product(),
            Schema::Mat(r, c) => r * c,
            _ => 0
        }
    } else {
        0
    }
}
