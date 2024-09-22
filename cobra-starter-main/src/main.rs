use core::panic;
use std::env;
use std::fs::File;
use std::io::prelude::*;

use sexp::Atom::*;
use sexp::*;

use im::HashMap;
use std::collections::HashSet;

use regex::Regex;

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
    RDI,
    RSI,
    R10,
}

#[derive(Debug)]
enum Instr {
    IMov(Val, Val),
    IAdd(Val, Val),
    ISub(Val, Val),
    IMul(Val, Val),
    ITag(String),
    IJump(String),
    IJumpEqual(String),
    ICmp(Val, Val),
    ICMovEqual(Val, Val),
    ICMovLess(Val, Val),
    ICMovLessEqual(Val, Val),
    ICMovGreater(Val, Val),
    ICMovGreaterEqual(Val, Val),
    ICall(String),
    IJumpOverflow(String),
}

#[derive(Debug, PartialEq, Eq)]
enum Op1 {
    Add1,
    Sub1,
}

#[derive(Debug, PartialEq, Eq)]
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

#[repr(i32)] // Specify the representation
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum ExprType {
    Number = 0,
    Boolean = 1,
}

impl ExprType {
    fn to_i32(&self) -> i32 {
        match self {
            ExprType::Number => 0,
            ExprType::Boolean => 1,
        }
    }
}

type VariableScope = HashMap<String, (i32, ExprType)>;
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

fn is_valid_identifier(s: &str) -> bool {
    if RESERVED_KEYWORDS.contains(&s) { return false; }

    let number_regex = Regex::new(r"^\d+(\.\d+)?$").unwrap();
    if number_regex.is_match(s) { return false; }

    return true;
}

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
                if !is_valid_identifier(str) {
                    panic!("Invalid program: variable name is not a valid identifier");
                } else {
                    Expr::Id(str.clone())
                }
            }
        }
        Sexp::Atom(Atom::I(x)) => {
            match i32::try_from(*x) {
                Ok(val) => Expr::Number(val),
                Err(_) => panic!("Invalid number; cannot convert to i32"),
            }
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

/// Compiling Exprs

fn push_rax_to_stack(instr_vec: &mut Vec<Instr>, rsp_offset: i32) -> i32 {
    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RSP, rsp_offset + SIZE_OF_NUMBER),
        Val::Reg(Reg::RAX),
    ));
    rsp_offset + SIZE_OF_NUMBER
}

fn compile_to_instrs(
    e: &Expr,
    scope: &mut VariableScope,
    instr_vec: &mut Vec<Instr>,
    rsp_offset: &mut i32,
    tag_id: &mut i32,
) -> ExprType {
    match e {
        Expr::Boolean(b) => {
            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::Imm(if *b { 1 } else { 0 }),
            ));
            ExprType::Boolean
        }
        Expr::Number(n) => {
            instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(*n)));
            ExprType::Number
        }
        Expr::Id(s) => {
            if s == "input" {
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RSP, SIZE_OF_NUMBER),
                ));

                ExprType::Number
            } else {
                match scope.get(s) {
                    Some((s_rsp_offset, e_type)) => {
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, *s_rsp_offset),
                        ));

                        *e_type
                    }
                    None => panic!("Unbound variable identifier {s}"),
                }
            }
        }
        Expr::UnOp(op, e) => {
            let e_type = compile_to_instrs(e, scope, instr_vec, rsp_offset, tag_id);

            if e_type != ExprType::Number {
                panic!("Invalid type for unary operation");
            }

            match op {
                Op1::Add1 => instr_vec.push(Instr::IAdd(Val::Reg(Reg::RAX), Val::Imm(1))),
                Op1::Sub1 => instr_vec.push(Instr::ISub(Val::Reg(Reg::RAX), Val::Imm(1))),
            };

            instr_vec.push(Instr::IJumpOverflow("overflow_error".to_string()));

            ExprType::Number
        }
        Expr::BinOp(op, e1, e2) => {
            // Compile e2 first so that subtraction works nicely, leaves e1 in rax
            let e2_type = compile_to_instrs(e2, scope, instr_vec, rsp_offset, tag_id);
            let rsp_offset_e2_eval = push_rax_to_stack(instr_vec, *rsp_offset);
            *rsp_offset = rsp_offset_e2_eval;

            let e1_type = compile_to_instrs(e1, scope, instr_vec, rsp_offset, tag_id); // e1 is in rax

            // Perform some type checking on the arguments
            if *op == Op2::Equal && e1_type != e2_type {
                panic!("Type mismatch in equality comparison");
            } else if e1_type != ExprType::Number || e2_type != ExprType::Number {
                panic!("Type mismatch for binary operation {:?}", op);
            }

            if matches!(
                op,
                Op2::Equal | Op2::Less | Op2::LessEqual | Op2::Greater | Op2::GreaterEqual
            ) {
                match op {
                    Op2::Equal => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));

                        instr_vec.push(Instr::ICMovEqual(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::Less => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));

                        instr_vec.push(Instr::ICMovLess(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::LessEqual => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));

                        instr_vec.push(Instr::ICMovLessEqual(
                            Val::Reg(Reg::RAX),
                            Val::Reg(Reg::R10),
                        ));
                    }
                    Op2::Greater => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));

                        instr_vec.push(Instr::ICMovGreater(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::GreaterEqual => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));

                        instr_vec.push(Instr::ICMovGreaterEqual(
                            Val::Reg(Reg::RAX),
                            Val::Reg(Reg::R10),
                        ));
                    }
                    _ => unreachable!(),
                }

                return ExprType::Boolean;
            } else if matches!(op, Op2::Plus | Op2::Minus | Op2::Times) {
                match op {
                    Op2::Plus => {
                        instr_vec.push(Instr::IAdd(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));
                    }
                    Op2::Minus => {
                        instr_vec.push(Instr::ISub(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));
                    }
                    Op2::Times => {
                        instr_vec.push(Instr::IMul(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));
                    }
                    _ => unreachable!(),
                }

                instr_vec.push(Instr::IJumpOverflow("overflow_error".to_string()));
                return ExprType::Number;
            } else {
                panic!("Invalid binary operation {:?}", op);
            }
        }
        Expr::Let(bindings, e) => {
            let original_scope = scope.clone();

            // Add the bindings from the scope
            let mut existing_identifiers: HashSet<String> = HashSet::new();

            for (var, var_e) in bindings {
                if var == "input" {
                    panic!("Reserved keyword input used as variable name in let expression");
                }

                let var_e_type = compile_to_instrs(var_e, scope, instr_vec, rsp_offset, tag_id);
                *rsp_offset = push_rax_to_stack(instr_vec, *rsp_offset);

                if existing_identifiers.contains(var) {
                    panic!("Duplicate binding");
                } else {
                    existing_identifiers.insert(var.clone());
                    scope.insert(var.clone(), (*rsp_offset, var_e_type));
                }
            }

            // Compile the expression
            let e_type = compile_to_instrs(e, scope, instr_vec, rsp_offset, tag_id);

            // Restore original scope after the let expression is finished
            *scope = original_scope;

            e_type
        }
        Expr::Set(id, e1) => {
            let e1_type = compile_to_instrs(e1, scope, instr_vec, rsp_offset, tag_id);
            let (id_offset, _) = scope.get(id).unwrap();

            instr_vec.push(Instr::IMov(
                Val::RegOffset(Reg::RSP, *id_offset),
                Val::Reg(Reg::RAX),
            ));
            // scope.insert(id.clone(), (*rsp_offset, e1_type)); // Update the stack offset for variable 'id'

            e1_type
        }
        Expr::Block(expr_vec) => {
            let mut last_e_type = ExprType::Number;

            for e in expr_vec {
                last_e_type = compile_to_instrs(e, scope, instr_vec, rsp_offset, tag_id);
            }

            last_e_type
        }
        Expr::If(e1, e2, e3) => {
            let curr_tag_id = *tag_id;

            *tag_id += 1;
            // Compile e1
            compile_to_instrs(e1, scope, instr_vec, rsp_offset, tag_id);

            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            // If e1 evaluates to false, go to e3
            instr_vec.push(Instr::IJumpEqual(format!("else{curr_tag_id}")));

            // Compile e2
            let return_type = compile_to_instrs(e2, scope, instr_vec, rsp_offset, tag_id);
            instr_vec.push(Instr::IJump(format!("end{curr_tag_id}")));

            // Compile e3
            instr_vec.push(Instr::ITag(format!("else{curr_tag_id}")));

            compile_to_instrs(e3, scope, instr_vec, rsp_offset, tag_id);

            instr_vec.push(Instr::IJump(format!("end{curr_tag_id}")));
            instr_vec.push(Instr::ITag(format!("end{curr_tag_id}")));

            return_type
        }
        Expr::RepeatUntil(e1, e2) => {
            let curr_tag_id = *tag_id;

            *tag_id += 1;
            // Do-while loop
            instr_vec.push(Instr::ITag(format!("loop{curr_tag_id}")));
            // Compile e1
            let return_type = compile_to_instrs(e1, scope, instr_vec, rsp_offset, tag_id);
            let rsp_offset_return = push_rax_to_stack(instr_vec, *rsp_offset);
            *rsp_offset = rsp_offset_return;

            // Compile e2
            compile_to_instrs(e2, scope, instr_vec, rsp_offset, tag_id);
            // If e2 returned false, keep going
            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            instr_vec.push(Instr::IJumpEqual(format!("loop{curr_tag_id}")));

            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RSP, rsp_offset_return),
            ));

            instr_vec.push(Instr::ITag(format!("end{curr_tag_id}")));

            return_type
        }
    }
}

fn compile_instrs_to_str(instr_vec: &Vec<Instr>) -> String {
    let n_spaces_indentation = 2;

    instr_vec
        .iter()
        .map(instr_to_str)
        .map(|s| format!("{}{}", " ".repeat(n_spaces_indentation), s))
        .collect::<Vec<String>>()
        .join("\n")
}

fn compile(e: &Expr) -> String {
    let scope = &mut VariableScope::new();
    let mut instr_vec: Vec<Instr> = Vec::new();
    let mut rsp_offset = SIZE_OF_NUMBER;
    let mut tag_id = 0;

    // Push the input value to the stack
    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RSP, SIZE_OF_NUMBER),
        Val::Reg(Reg::RDI),
    ));

    let return_type = compile_to_instrs(e, scope, &mut instr_vec, &mut rsp_offset, &mut tag_id);

    // Call print function with final result
    instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
    instr_vec.push(Instr::IMov(
        Val::Reg(Reg::RSI),
        Val::Imm(return_type.to_i32()),
    ));
    instr_vec.push(Instr::ICall("snek_print".to_string()));

    // Turn the instructions into a multi-line string
    compile_instrs_to_str(&instr_vec)
}

fn instr_to_str(i: &Instr) -> String {
    match i {
        Instr::IMov(dst, src) => format!("mov {}, {}", val_to_str(dst), val_to_str(src)),
        Instr::IAdd(v1, v2) => format!("add {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ISub(v1, v2) => format!("sub {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::IMul(v1, v2) => format!("imul {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ITag(tag) => format!("{tag}:"),
        Instr::IJump(tag) => format!("jmp {tag}"),
        Instr::IJumpEqual(tag) => format!("je {tag}"),
        Instr::ICmp(v1, v2) => format!("cmp {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ICMovEqual(v1, v2) => format!("cmove {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ICMovLess(v1, v2) => format!("cmovl {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ICMovLessEqual(v1, v2) => format!("cmovle {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ICMovGreater(v1, v2) => format!("cmovg {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ICMovGreaterEqual(v1, v2) => {
            format!("cmovge {}, {}", val_to_str(v1), val_to_str(v2))
        }
        Instr::ICall(fn_name) => format!("call {}", fn_name),
        Instr::IJumpOverflow(fn_name) => format!("jo {}", fn_name),
    }
}

fn reg_to_str(r: &Reg) -> String {
    match r {
        Reg::RAX => "rax".to_string(),
        Reg::RSP => "rsp".to_string(),
        Reg::RDI => "rdi".to_string(),
        Reg::RSI => "rsi".to_string(),
        Reg::R10 => "r10".to_string(),
    }
}

fn val_to_str(v: &Val) -> String {
    match v {
        Val::Reg(r) => reg_to_str(r),
        Val::Imm(i) => format!("{}", i),
        Val::RegOffset(r, i) => {
            if *i == 0 {
                format!("[{}]", reg_to_str(r))
            } else {
                format!("[{}-{v}]", reg_to_str(r), v = i)
            }
        }
    }
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();

    let in_name = &args[1];
    let out_name = &args[2];

    let mut in_file = File::open(in_name)?;
    let mut in_contents = String::new();
    in_file.read_to_string(&mut in_contents)?;

    // You will make result hold the result of actually compiling
    let result = compile(&parse_expr(&parse(&in_contents).unwrap()));

    let asm_program = format!(
        "
extern snek_print
extern snek_error

section .text
global our_code_starts_here

overflow_error:
  mov rdi, 3
  call snek_error

our_code_starts_here:
{}
  ret
",
        result
    );

    let mut out_file = File::create(out_name)?;
    out_file.write_all(asm_program.as_bytes())?;

    Ok(())

    // let in_name = "/Users/micahreich/Documents/17363/cobra-starter-main/tests/example1.snek";
    // // let out_name = &args[2];

    // let mut in_file = File::open(in_name)?;
    // let mut in_contents = String::new();
    // in_file.read_to_string(&mut in_contents)?;

    // // You will make result hold the result of actually compiling
    // let parsed_contents = parse(&in_contents).unwrap();
    // println!("{}", parsed_contents);

    // let parsed_expr = parse_expr(&parsed_contents);
    // println!("{:?}", parsed_expr);

    // Ok(())
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
