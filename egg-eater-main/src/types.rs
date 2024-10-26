use std::str::FromStr;

use im::HashMap;
use regex::Regex;

#[derive(Debug)]
pub enum Val {
    Reg(Reg),
    Imm(i32),
    RegOffset(Reg, i32),
    RegOffsetImm(Reg, i32),
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum Reg {
    RAX,
    RSP,
    RBP,
    RDI,
    RSI,
    R10,
    R11,
}

#[derive(Debug)]
pub enum Instr {
    IMov(Val, Val),
    IAdd(Val, Val),
    ISub(Val, Val),
    IMul(Val, Val),
    IAnd(Val, Val),
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
    IPush(Val),
    IPop(Val),
    IRet,
}

pub const FUNCTION_PROLOGUE: [Instr; 2] = [
    Instr::IPush(Val::Reg(Reg::RBP)), // push old rbp to stack
    Instr::IMov(Val::Reg(Reg::RBP), Val::Reg(Reg::RSP)), // set rbp equal to the current rsp
                                      // Instr::IPush(Val::Reg(Reg::RBX)), // save rbx on the stack
];

pub const FUNCTION_EPILOGUE: [Instr; 3] = [
    // Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, -SIZE_OF_NUMBER)), // restore rbx
    Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::RBP)),
    Instr::IPop(Val::Reg(Reg::RBP)),
    Instr::IRet,
];

pub const ALIGN_RSP_16_BYTES: Instr =
    Instr::IAnd(Val::Reg(Reg::RSP), Val::Imm(0xFFFFFFF0u32 as i32));

pub const MAIN_FN_TAG: &str = "our_code_starts_here";

#[derive(Debug, PartialEq, Eq)]
pub enum Op1 {
    Add1,
    Sub1,
    Print,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Op2 {
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
pub enum Expr {
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
    Call(FunctionSignature, Vec<Expr>),
}

#[repr(i32)] // Specify the representation
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ExprType {
    Number = 0,
    Boolean = 1,
    Main = 2,
}

impl ExprType {
    pub fn to_type_flag(self) -> i32 {
        match self {
            ExprType::Number => 0,
            ExprType::Boolean => 1,
            ExprType::Main => 2,
        }
    }
}

impl FromStr for ExprType {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "int" => Ok(ExprType::Number),
            "bool" => Ok(ExprType::Boolean),
            _ => Err(format!("Unexpected type: {}", s)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub name: String,
    pub arg_types: Vec<(String, ExprType)>,
    pub return_type: ExprType,
}

pub struct Function {
    pub signature: FunctionSignature,
    pub body: Box<Expr>,
}

pub type Prog = Vec<Function>;

pub type VariableScope = HashMap<String, (i32, ExprType)>;
pub const SIZE_OF_NUMBER: i32 = 8;

pub const RESERVED_KEYWORDS: [&str; 17] = [
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

pub fn is_valid_identifier(s: &str) -> bool {
    if RESERVED_KEYWORDS.into_iter().any(|k| k == s) {
        return false;
    }

    let number_regex = Regex::new(r"^\d+(\.\d+)?$").unwrap();
    if number_regex.is_match(s) {
        return false;
    }

    true
}

pub fn round_up_to_next_multiple_of_16(n: i32) -> i32 {
    (n + 15) & !15
}
