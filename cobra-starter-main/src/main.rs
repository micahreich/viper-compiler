use core::panic;
use std::env;
use std::fs::File;
use std::io::prelude::*;

use sexp::Atom::*;
use sexp::*;

use im::HashMap;
use std::collections::HashSet;

#[derive(Debug)]
enum Val {
    Reg(Reg),
    Imm(i32),
    RegOffset(Reg, i32),
}

#[derive(Debug)]
enum Reg {
    RAX,
    RSP,
}

#[derive(Debug)]
enum Instr {
    IMov(Val, Val),
    IAdd(Val, Val),
    ISub(Val, Val),
    IMul(Val, Val),
}

#[derive(Debug)]
enum Op1 {
    Add1,
    Sub1,
}

#[derive(Debug)]
enum Op2 {
    Plus,
    Minus,
    Times,
    Equal,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
}

#[derive(Debug)]
enum Expr {
    Number(i32),
    Boolean(bool),
    Id(String),
    Let(Vec<(String, Expr)>, Box<Expr>),
    UnOp(Op1, Box<Expr>),
    BinOp(Op2, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    RepeatUntil(Box<Expr>, Box<Expr>),
    Set(String, Box<Expr>),
    Block(Vec<Expr>),
}

type VariableScope = HashMap<String, i32>;
const SIZE_OF_NUMBER: i32 = 8;

const RESERVED_KEYWORDS: [&str; 17] = [
    "let",
    "set!",
    "if",
    "block",
    "repeat-until",
    "true",
    "false",
    "+",
    "-",
    "*",
    "<",
    "<=",
    ">",
    ">=",
    "=",
    "add1",
    "sub1",
];

/// Parsing expressions

fn parse_let_expr(b_vec_sexp: &Sexp, expr_sexp: &Sexp) -> Expr {
    match b_vec_sexp {
        Sexp::List(vec) => {
            let bindings_vector: Vec<(String, Expr)> = vec.into_iter().map(|sexp_list| {
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

fn parse_block_expr(e_vec_sexp: &[Sexp]) -> Expr {
    let expression_vec: Vec<Expr> = e_vec_sexp
        .into_iter()
        .map(|sexp| parse_expr(sexp))
        .collect();

    Expr::Block(expression_vec)
}

fn parse_expr(s: &Sexp) -> Expr {
    match s {
        Sexp::Atom(Atom::F(_)) => panic!("Invalid program: floats are not allowed"),
        Sexp::Atom(Atom::S(str)) => {
            if str == "true" {
                Expr::Boolean(true)
            } else if str == "false" {
                Expr::Boolean(false)
            } else {
                if RESERVED_KEYWORDS.iter().any(|&s| s == str) {
                    panic!("Invalid program: variable name is a reserved keyword");
                } else {
                    Expr::Id(str.clone())
                }
            }
        }
        Sexp::Atom(Atom::I(x)) => Expr::Number(i32::try_from(*x).unwrap()),
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
                Sexp::Atom(S(op)) if op == "block" => {
                    parse_block_expr(&vec[1..])
                }
                _ => panic!("Invalid program: malformed expression"),
            },
        },
    }
}

/// Compiling Exprs

fn push_rax_to_stack(instr_vec: &mut Vec<Instr>, rsp_offset: i32) -> i32 {
    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RSP, rsp_offset + SIZE_OF_NUMBER),
        Val::Reg(Reg::RAX),
    ));
    rsp_offset + SIZE_OF_NUMBER
}

/*
fn compile_to_instrs(
    e: &Expr,
    scope: &mut VariableScope,
    instr_vec: &mut Vec<Instr>,
    rsp_offset: &mut i32,
) {
    match e {
        Expr::Number(n) => {
            instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(*n)));
        }
        Expr::Id(s) => match scope.get(s) {
            Some(s_rsp_offset) => {
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RSP, *s_rsp_offset),
                ));
            }
            None => panic!("Unbound variable identifier {s}"),
        },
        Expr::UnOp(op, e) => {
            compile_to_instrs(e, scope, instr_vec, rsp_offset);

            match op {
                Op1::Add1 => instr_vec.push(Instr::IAdd(Val::Reg(Reg::RAX), Val::Imm(1))),
                Op1::Sub1 => instr_vec.push(Instr::ISub(Val::Reg(Reg::RAX), Val::Imm(1))),
            };
        }
        Expr::BinOp(op, e1, e2) => {
            // Compile e2 first so that subtraction works nicely, leaves e1 in rax
            compile_to_instrs(e2, scope, instr_vec, rsp_offset);
            let rsp_offset_e2_eval = push_rax_to_stack(instr_vec, *rsp_offset);
            *rsp_offset = rsp_offset_e2_eval;

            compile_to_instrs(e1, scope, instr_vec, rsp_offset); // e1 is in rax

            match op {
                Op2::Plus => instr_vec.push(Instr::IAdd(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                )),
                Op2::Minus => instr_vec.push(Instr::ISub(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                )),
                Op2::Times => instr_vec.push(Instr::IMul(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                )),
            }
        }
        Expr::Let(bindings, e) => {
            let original_scope = scope.clone();

            // Add the bindings from the scope
            let mut existing_identifiers: HashSet<String> = HashSet::new();

            for (var, var_e) in bindings {
                compile_to_instrs(var_e, scope, instr_vec, rsp_offset);
                *rsp_offset = push_rax_to_stack(instr_vec, *rsp_offset);

                if existing_identifiers.contains(var) {
                    panic!("Duplicate binding");
                } else {
                    existing_identifiers.insert(var.clone());
                    scope.insert(var.clone(), *rsp_offset);
                }
            }

            // Compile the expression
            compile_to_instrs(e, scope, instr_vec, rsp_offset);

            // Restore original scope after the let expression is finished
            *scope = original_scope;
        }
    }
}

fn compile_instrs_to_str(instr_vec: &Vec<Instr>) -> String {
    let n_spaces_indentation = 2;

    instr_vec
        .iter()
        .map(|i| instr_to_str(i))
        .map(|s| format!("{}{}", " ".repeat(n_spaces_indentation), s))
        .collect::<Vec<String>>()
        .join("\n")
}

fn compile(e: &Expr) -> String {
    let scope = &mut VariableScope::new();
    let mut instr_vec: Vec<Instr> = Vec::new();
    let mut rsp_offset = 0;

    compile_to_instrs(e, scope, &mut instr_vec, &mut rsp_offset);
    compile_instrs_to_str(&instr_vec)
}

fn instr_to_str(i: &Instr) -> String {
    match i {
        Instr::IMov(dst, src) => format!("mov {}, {}", val_to_str(dst), val_to_str(src)),
        Instr::IAdd(v1, v2) => format!("add {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ISub(v1, v2) => format!("sub {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::IMul(v1, v2) => format!("imul {}, {}", val_to_str(v1), val_to_str(v2)),
    }
}

fn reg_to_str(r: &Reg) -> String {
    match r {
        Reg::RAX => "rax".to_string(),
        Reg::RSP => "rsp".to_string(),
    }
}

fn val_to_str(v: &Val) -> String {
    match v {
        Val::Reg(r) => reg_to_str(r),
        Val::Imm(i) => format!("{}", i),
        Val::RegOffset(r, i) => format!("[{}-{i}]", reg_to_str(r), i = i),
    }
}
*/

fn main() -> std::io::Result<()> {
    //     let args: Vec<String> = env::args().collect();

    //     let in_name = &args[1];
    //     let out_name = &args[2];

    //     let mut in_file = File::open(in_name)?;
    //     let mut in_contents = String::new();
    //     in_file.read_to_string(&mut in_contents)?;

    //     // You will make result hold the result of actually compiling
    //     let result = compile(&parse_expr(&parse(&in_contents).unwrap()));

    //     let asm_program = format!(
    //         "
    // section .text
    // global our_code_starts_here
    // our_code_starts_here:
    // {}
    //   ret
    // ",
    //         result
    //     );

    //     let mut out_file = File::create(out_name)?;
    //     out_file.write_all(asm_program.as_bytes())?;

    //     Ok(())

    let in_name = "/Users/micahreich/Documents/17363/cobra-starter-main/tests/example1.snek";
    // let out_name = &args[2];

    let mut in_file = File::open(in_name)?;
    let mut in_contents = String::new();
    in_file.read_to_string(&mut in_contents)?;

    // You will make result hold the result of actually compiling
    let parsed_contents = parse(&in_contents).unwrap();
    println!("{}", parsed_contents);

    let parsed_expr = parse_expr(&parsed_contents);
    println!("{:?}", parsed_expr);

    Ok(())
}

// List(
//     vec![
//         Atom("let"),
//         List(vec![
//             List(vec![Atom("x"), Atom("5")])
//         ]),
//         Atom("x")
//     ]
// )

// List(
//     Atom(let),
//     List(List(Atom(x), Atom(5)), List(Atom(y), Atom(7))),
//     List(Atom(+), Atom(x), Atom(y))
// )
