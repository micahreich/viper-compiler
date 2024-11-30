use std::str::FromStr;

use im::{HashMap, HashSet};
use regex::Regex;

pub const MAIN_FN_TAG: &str = "our_code_starts_here";

pub type ProgramFunctions = Vec<Function>;
pub type ProgramClasses = Vec<Class>;

pub type VariableScope = HashMap<String, (i32, ExprType)>;
pub const SIZE_OF_DWORD: i32 = 8;

pub const MAX_HEAP_SIZE_R12_OFFSET: i32 = -16;
pub const CURRENT_HEAP_SIZE_R12_OFFSET: i32 = -24;

pub const BASE_CLASS_NAME: &str = "Object";

pub const FUNCTION_EPILOGUE: [Instr; 2] = [
    Instr::ILeave,
    Instr::IRet
];

pub const RESERVED_KEYWORDS: [&str; 19] = [
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
    "lookup",
    "input",
];

#[derive(Debug, Clone)]
pub enum Val {
    Reg(Reg),
    Imm(i32),
    RegOffset(Reg, i32),
}

#[derive(Debug, Clone)]
#[allow(non_camel_case_types)]
pub enum Reg {
    RAX,
    RSP,
    RBP,
    RDI,
    RSI,
    R10,
    R11,
    R12,
    R13,
    RBX,
}

#[derive(Debug, Clone)]
pub enum Instr {
    IMov(Val, Val),
    IAdd(Val, Val),
    ISub(Val, Val),
    IMul(Val, Val),
    IAnd(Val, Val),
    ITag(String),
    IJump(String),
    IJumpEqual(String),
    IJumpNotEqual(String),
    IJumpLess(String),
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
    IComment(String),
    IEnter(i32),
    ILeave,
    ISyscall,
    IDq(String),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Op1 {
    Add1,
    Sub1,
    Print,
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

#[derive(Debug, Clone)]
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
    RecordSetField(String, String, Box<Expr>),
    Block(Vec<Expr>),
    RecordInitializer(String, Vec<Expr>), // acts like a pointer to the record type
    Call(FunctionSignature, Vec<Expr>),
    Lookup(Box<Expr>, String), // recordpointer, fieldname
}

#[repr(i32)] // Specify the representation
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum ExprType {
    Number = 0,
    Boolean = 1,
    RecordPointer(String) = 2,
    Main = 3,
    RecordNullPtr = 4,
}

impl ExprType {
    pub fn to_type_flag(&self) -> i32 {
        match self {
            ExprType::Number => 0,
            ExprType::Boolean => 1,
            ExprType::RecordPointer(_) => 2,
            ExprType::Main => 3,
            ExprType::RecordNullPtr => 4,
        }
    }
}

impl FromStr for ExprType {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "int" => Ok(ExprType::Number),
            "bool" => Ok(ExprType::Boolean),
            _ => Ok(ExprType::RecordPointer(s.to_string())),
        }
    }
}

#[derive(Debug, Clone)]
pub struct RecordSignature {
    pub name: String,
    pub field_types: Vec<(String, ExprType)>,
}

#[derive(Debug, Clone)]
pub struct ClassSignature {
    pub name: String,
    pub inherits: String,
    pub field_types: Vec<(String, ExprType)>,
    pub method_signatures: HashMap<String, FunctionSignature>,
    /// Mapping from method name to vtable index, resolved method name (may be from inherited class)
    pub vtable_indices: HashMap<String, (usize, String)>
}

#[derive(Debug, Clone, Hash)]
pub struct FunctionSignature {
    pub name: String,
    pub arg_types: Vec<(String, ExprType)>,
    pub return_type: ExprType,
}

#[derive(Clone)]
pub struct Function {
    pub signature: FunctionSignature,
    pub body: Box<Expr>,
}

#[derive(Clone)]
pub struct Class {
    pub signature: ClassSignature,
    pub methods: HashMap<String, Function>,
}

pub struct ProgDefns {
    pub fn_signatures: HashMap<String, FunctionSignature>,
    pub record_signatures: HashMap<String, RecordSignature>,
    pub class_signatures: HashMap<String, ClassSignature>
}

pub struct Program {
    pub functions: HashMap<String, Function>,
    pub classes: HashMap<String, Class>,
    pub main_expr: Box<Expr>,
}

pub struct CompileCtx {
    pub scope: VariableScope,
    pub rbp_offset: i32,
    pub rbx_offset: i32,
    pub tag_id: i32,
}

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