use core::panic;
// use prettydiff::format_table::new;
use sexp::Atom::*;
use sexp::*;

use crate::types::*;

pub fn parse_let_expr(b_vec_sexp: &Sexp, expr_sexp: &Sexp) -> Expr {
    match b_vec_sexp {
        Sexp::List(vec) => {
            let bindings_vector: Vec<(String, Expr)> = vec.iter().map(|sexp_list| {
                match sexp_list {
                    Sexp::List(vec) => match &vec[..] {
                        [Sexp::Atom(S(identifier)), e] => (identifier.clone(), parse_expr(e)),
                        _ => panic!("Invalid let expression: bindings must be of the form (<identifier> <expr>)"),
                    },
                    _ => panic!("Invalid let expression: bindings must be of the form (<identifier> <expr>)"),
                }
            })
            .collect();

            Expr::Let(bindings_vector, Box::new(parse_expr(expr_sexp)))
        }
        _ => panic!("Invalid program: malformed let expression (are you missing parens?)"),
    }
}

pub fn parse_block_expr(e_vec_sexp: &[Sexp]) -> Expr {
    let expression_vec: Vec<Expr> = e_vec_sexp.iter().map(parse_expr).collect();

    Expr::Block(expression_vec)
}

pub fn parse_expr(s: &Sexp) -> Expr {
    match s {
        Sexp::Atom(Atom::F(_)) => panic!("Invalid program: floats are not allowed"),
        Sexp::Atom(Atom::S(str)) => {
            if str == "true" {
                Expr::Boolean(true)
            } else if str == "false" {
                Expr::Boolean(false)
            } else if !is_valid_identifier(str) {
                panic!("Invalid program: variable name is a reserved keyword");
            } else {
                Expr::Id(str.clone())
            }
        }
        Sexp::Atom(Atom::I(x)) => match i32::try_from(*x) {
            Ok(val) => Expr::Number(val),
            Err(_) => panic!("Invalid number; cannot convert to i32"),
        },
        Sexp::List(vec) => match &vec[..] {
            [Sexp::Atom(S(op)), e] if op == "add1" => {
                Expr::UnOp(Op1::Add1, Box::new(parse_expr(e)))
            }
            [Sexp::Atom(S(op)), e] if op == "sub1" => {
                Expr::UnOp(Op1::Sub1, Box::new(parse_expr(e)))
            }
            [Sexp::Atom(S(op)), e1, e2] if op == "+" => Expr::BinOp(
                Op2::Plus,
                Box::new(parse_expr(e1)),
                Box::new(parse_expr(e2)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "-" => Expr::BinOp(
                Op2::Minus,
                Box::new(parse_expr(e1)),
                Box::new(parse_expr(e2)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "*" => Expr::BinOp(
                Op2::Times,
                Box::new(parse_expr(e1)),
                Box::new(parse_expr(e2)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "<" => Expr::BinOp(
                Op2::Less,
                Box::new(parse_expr(e1)),
                Box::new(parse_expr(e2)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "<=" => Expr::BinOp(
                Op2::LessEqual,
                Box::new(parse_expr(e1)),
                Box::new(parse_expr(e2)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == ">" => Expr::BinOp(
                Op2::Greater,
                Box::new(parse_expr(e1)),
                Box::new(parse_expr(e2)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == ">=" => Expr::BinOp(
                Op2::GreaterEqual,
                Box::new(parse_expr(e1)),
                Box::new(parse_expr(e2)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "=" => Expr::BinOp(
                Op2::Equal,
                Box::new(parse_expr(e1)),
                Box::new(parse_expr(e2)),
            ),
            [Sexp::Atom(S(op)), b_vec, e] if op == "let" => parse_let_expr(b_vec, e),
            [Sexp::Atom(S(op)), Sexp::Atom(S(name)), e1] if op == "set!" => {
                Expr::Set(name.clone(), Box::new(parse_expr(e1)))
            }
            [Sexp::Atom(S(op)), e1, e2, e3] if op == "if" => Expr::If(
                Box::new(parse_expr(e1)),
                Box::new(parse_expr(e2)),
                Box::new(parse_expr(e3)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "repeat-until" => {
                Expr::RepeatUntil(Box::new(parse_expr(e1)), Box::new(parse_expr(e2)))
            }
            _ => match &vec[0] {
                Sexp::Atom(S(op)) if op == "block" => parse_block_expr(&vec[1..]),
                _ => panic!("Invalid program: malformed expression"),
            },
        },
    }
}

pub fn parse_type(s: &Sexp) -> ExprType {
    match s {
        Sexp::Atom(S(type_name)) => type_name.parse().unwrap(),
        _ => panic!("Unexpected type"),
    }
}

pub fn parse_argument(s: &Sexp) -> (String, ExprType) {
    match s {
        Sexp::Atom(_) => panic!("Malformed function argument"),
        Sexp::List(vec) => {
            if vec.len() != 2 {
                panic!("Malformed function argument");
            }

            let arg_name = match &vec[0] {
                Sexp::Atom(S(name)) => name,
                _ => panic!("Malformed function argument"),
            };

            let arg_type = parse_type(&vec[1]);

            (arg_name.to_string(), arg_type)
        }
    }
}

pub fn parse_defn(s: &Sexp) -> Function {
    // Right now this function only works for pasing functions, will need to update
    // if defintions ever contain more than functions

    match s {
        Sexp::Atom(_) => panic!("Malformed definition"),
        Sexp::List(vec) => {
            match &vec[0] {
                Sexp::Atom(S(name)) => {
                    if !DEFINITIONS.into_iter().any(|k| k == name) {
                        panic!("Malformed definition")
                    }
                }
                _ => panic!("Malformed definition"),
            }

            let func_name = match &vec[1] {
                Sexp::Atom(S(name)) => name,
                _ => panic!("Malformed definition"),
            };

            let func_expr = parse_expr(&vec[vec.len() - 1]);
            let func_type = parse_type(&vec[vec.len() - 2]);

            let mut func_args: Vec<(String, ExprType)> = Vec::new();

            for s1 in &vec[2..vec.len() - 2] {
                func_args.push(parse_argument(s1));
            }

            // func_name.to_string(), func_args, func_type, Box::new(func_expr)

            Function {
                name: func_name.to_string(),
                arg_types: func_args,
                return_type: func_type,
                body: Box::new(func_expr),
            }
        }
    }
}

pub fn parse_prog(s: &Sexp) -> Prog {
    // Prog is made up of a series of definitions (funcs) and an expression
    let mut definitions: Vec<Function> = Vec::new();

    match s {
        Sexp::Atom(_) => panic!("Malformed program"),
        Sexp::List(vec) => {
            for s1 in vec {
                match s1 {
                    Sexp::Atom(_) => definitions.push(Function {
                        name: "main".to_string(),
                        arg_types: Vec::new(),
                        return_type: ExprType::Main,
                        body: Box::new(parse_expr(s1)),
                    }),
                    Sexp::List(sub_vec) => match &sub_vec[0] {
                        Sexp::Atom(S(name)) if DEFINITIONS.into_iter().any(|k| k == name) => {
                            definitions.push(parse_defn(&s1))
                        }
                        Sexp::Atom(_) => definitions.push(Function {
                            name: "main".to_string(),
                            arg_types: Vec::new(),
                            return_type: ExprType::Main,
                            body: Box::new(parse_expr(s1)),
                        }),
                        _ => panic!("Malformed program"),
                    },
                }
            }
        }
    }

    definitions
}
