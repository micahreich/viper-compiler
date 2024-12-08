use std::borrow::Cow;
use std::collections::{HashMap, VecDeque};

pub const MAIN_FN_TAG: &str = "our_code_starts_here";

pub type VariableScope = HashMap<String, (i32, ExprType)>;
pub const SIZE_OF_DWORD: i32 = 8;

pub const MAX_HEAP_SIZE_R12_OFFSET: i32 = -3 * SIZE_OF_DWORD;
pub const CURRENT_HEAP_SIZE_R12_OFFSET: i32 = -4 * SIZE_OF_DWORD;

pub const BASE_CLASS_NAME: &str = "Object";

pub const FUNCTION_EPILOGUE: [Instr; 2] = [Instr::ILeave, Instr::IRet];

pub const PRINT_OPEN_PARENS: [Instr; 3] = [
    Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(0)),
    Instr::IMov(Val::Reg(Reg::RSI), Val::Imm(1)),
    Instr::ICall(Cow::Borrowed("snek_print")),
];

pub const PRINT_CLOSED_PARENS: [Instr; 3] = [
    Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(1)),
    Instr::IMov(Val::Reg(Reg::RSI), Val::Imm(1)),
    Instr::ICall(Cow::Borrowed("snek_print")),
];

pub const PRINT_NEWLINE: [Instr; 2] = [
    Instr::IMov(Val::Reg(Reg::RSI), Val::Imm(0)),
    Instr::ICall(Cow::Borrowed("snek_print")),
];

pub const RESERVED_KEYWORDS: [&str; 20] = [
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
    "__tmp",
];

#[derive(Debug, Clone)]
pub enum Val {
    Reg(Reg),
    Imm(i32),
    RegOffset(Reg, i32),
    LabelPointer(String),
}

#[derive(Debug, Clone)]
#[allow(non_camel_case_types)]
pub enum Reg {
    RAX,
    RSP,
    RBP,
    RDI,
    RSI,
    R11,
    R12,
    R13,
    RBX,
}

#[derive(Debug, Clone)]
pub enum Instr<'a> {
    IMov(Val, Val),
    IAdd(Val, Val),
    ISub(Val, Val),
    IMul(Val, Val),
    ITag(Cow<'a, str>),
    IJump(Cow<'a, str>),
    IJumpEqual(Cow<'a, str>),
    IJumpNotEqual(Cow<'a, str>),
    IJumpLess(Cow<'a, str>),
    ICmp(Val, Val),
    ICMovEqual(Val, Val),
    ICMovLess(Val, Val),
    ICMovLessEqual(Val, Val),
    ICMovGreater(Val, Val),
    ICMovGreaterEqual(Val, Val),
    ICall(Cow<'a, str>),
    IJumpOverflow(Cow<'a, str>),
    IRet,
    IComment(Cow<'a, str>),
    IEnter(i32),
    ILeave,
    IDq(Cow<'a, str>),
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
    SetField(String, String, Box<Expr>),
    Block(Vec<Expr>),
    RecordInitializer(String, Vec<Expr>),
    ObjectInitializer(String, Vec<Expr>),
    Call(String, Vec<Expr>),
    CallMethod(String, String, Vec<Expr>),
    Lookup(Box<Expr>, String),
}

#[derive(Clone, Debug)]
pub enum SymbolType {
    Record(String),
    Class(String),
    Function(String),
}

impl SymbolType {
    pub fn from_stringified_type(keyword: &String, name: &String) -> Option<Self> {
        match keyword.as_str() {
            "record" => Some(SymbolType::Record(name.clone())),
            "class" => Some(SymbolType::Class(name.clone())),
            "fun" => Some(SymbolType::Function(name.clone())),
            _ => None,
        }
    }
}

pub struct SymbolTable {
    symbols: HashMap<String, SymbolType>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable {
            symbols: HashMap::new(),
        }
    }

    pub fn insert(&mut self, name: &String, symbol_type: SymbolType) {
        if self.symbols.insert(name.clone(), symbol_type).is_some() {
            panic!("Invalid program: symbol {name} already exists in symbol table");
        }
    }

    pub fn get(&self, name: &String) -> Option<&SymbolType> {
        self.symbols.get(name)
    }
}

#[repr(i32)] // Specify the representation
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum ExprType {
    Number = 0,
    Boolean = 1,
    RecordPointer(String) = 2,
    NullPtr = 4,
    ObjectPointer(String) = 5,
}

impl ExprType {
    pub fn from_stringified_type(s: &String, symbol_table: &SymbolTable) -> Self {
        match s.as_str() {
            "int" => ExprType::Number,
            "bool" => ExprType::Boolean,
            "NULL" => ExprType::NullPtr,
            _ => {
                match symbol_table.get(s) {
                    Some(SymbolType::Record(_)) => ExprType::RecordPointer(s.clone()),
                    Some(SymbolType::Class(_)) => ExprType::ObjectPointer(s.clone()),
                    _ => panic!("Invalid program: type {s} is neither a primitive type nor found in symbol table"),
                }
            }
        }
    }
}

impl ExprType {
    pub fn to_type_flag(&self) -> i32 {
        match self {
            ExprType::Number => 2,
            ExprType::Boolean => 3,
            ExprType::RecordPointer(_) => 4,
            ExprType::ObjectPointer(_) => 4,
            ExprType::NullPtr => 5,
        }
    }

    pub fn is_heap_allocated(&self) -> bool {
        match self {
            ExprType::RecordPointer(_) => true,
            ExprType::ObjectPointer(_) => true,
            _ => false,
        }
    }

    pub fn extract_heap_allocated_type_name(&self) -> String {
        match self {
            ExprType::RecordPointer(s) => s.clone(),
            ExprType::ObjectPointer(s) => s.clone(),
            _ => panic!("Cannot extract heap allocated type from non heap allocated type"),
        }
    }
}

pub trait HeapAllocated {
    fn name(&self) -> &String;
    fn field_types(&self) -> &Vec<(String, ExprType)>;
    fn alloc_size(&self) -> i32;
    fn field_idx_start(&self) -> i32;
}

#[derive(Debug, Clone)]
pub struct Record {
    pub name: String,
    pub field_types: Vec<(String, ExprType)>,
}

impl HeapAllocated for Record {
    fn name(&self) -> &String {
        &self.name
    }

    fn field_types(&self) -> &Vec<(String, ExprType)> {
        &self.field_types
    }

    fn alloc_size(&self) -> i32 {
        (self.field_types.len() + 1) as i32 * SIZE_OF_DWORD
    }

    fn field_idx_start(&self) -> i32 {
        1
    }
}

#[derive(Debug, Clone)]
pub struct ClassSignature {
    pub name: String,
    pub inherits: String,
    pub field_types: Vec<(String, ExprType)>,
}

#[derive(Debug, Clone, Hash)]
pub struct FunctionSignature {
    pub name: String,
    pub arg_types: Vec<(String, ExprType)>,
    pub return_type: ExprType,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub arg_types: Vec<(String, ExprType)>,
    pub return_type: ExprType,
    pub body: Box<Expr>,
}

#[derive(Clone, Debug)]
pub struct Class {
    pub name: String,
    pub inherits: String,
    pub field_types: Vec<(String, ExprType)>,
    /// Mapping from method name to method body, where the `name` part of the value is how the full
    /// method name appears in a vtable as a label in the assembly code
    pub methods: HashMap<String, Function>,
    /// Mapping from method name to vtable index, resolved method name (may be from inherited class)
    pub vtable_indices: HashMap<String, (usize, String)>,
}

impl Class {
    pub fn new(
        name: String,
        inherits: String,
        field_types: Vec<(String, ExprType)>,
        methods: HashMap<String, Function>,
    ) -> Class {
        Class {
            name,
            inherits,
            field_types,
            methods: methods,
            vtable_indices: HashMap::new(),
        }
    }
}

impl HeapAllocated for Class {
    fn name(&self) -> &String {
        &self.name
    }

    fn field_types(&self) -> &Vec<(String, ExprType)> {
        &self.field_types
    }

    fn alloc_size(&self) -> i32 {
        (self.field_types.len() + 2) as i32 * SIZE_OF_DWORD
    }

    fn field_idx_start(&self) -> i32 {
        2
    }
}

pub struct Program {
    pub functions: HashMap<String, Function>,
    pub classes: HashMap<String, Class>,
    pub records: HashMap<String, Record>,
    pub main_expr: Box<Expr>,
    inheritance_graph: Option<HashMap<String, Vec<String>>>,
}

impl Program {
    pub fn new() -> Program {
        Program {
            functions: HashMap::new(),
            classes: HashMap::new(),
            records: HashMap::new(),
            main_expr: Box::new(Expr::Number(0)),
            inheritance_graph: None,
        }
    }

    pub fn add_function(&mut self, function: Function) {
        self.functions.insert(function.name.clone(), function);
    }

    pub fn get_function(&self, name: &String) -> &Function {
        self.functions
            .get(name)
            .expect("Function {name} not found in program")
    }

    pub fn add_class(&mut self, class: Class) {
        self.classes.insert(class.name.clone(), class);
    }

    pub fn get_class(&self, name: &String) -> &Class {
        self.classes
            .get(name)
            .expect("Class {name} not found in program")
    }

    pub fn add_record(&mut self, record: Record) {
        self.records.insert(record.name.clone(), record);
    }

    pub fn get_record(&self, name: &String) -> &Record {
        self.records
            .get(name)
            .expect("Record {name} not found in program")
    }

    pub fn set_main_expr(&mut self, main_expr: Expr) {
        self.main_expr = Box::new(main_expr);
    }

    fn build_inheritance_graph(&mut self) {
        self.classes
            .keys()
            .chain(&[BASE_CLASS_NAME.to_string()])
            .for_each(|class| {
                self.inheritance_graph
                    .as_mut()
                    .unwrap()
                    .insert(class.clone(), Vec::new());
            });

        for class in self.classes.values_mut() {
            let parent = &class.inherits;
            let child = &class.name;

            let children = self
                .inheritance_graph
                .as_mut()
                .unwrap()
                .get_mut(parent)
                .expect("Parent class not found in inheritance graph");

            children.push(child.clone());
        }
    }

    fn topological_sort_inheritance_graph(graph: &HashMap<String, Vec<String>>) -> Result<Vec<String>, String> {
        // Step 1: Compute in-degrees
        let mut in_degree: HashMap<String, usize> = HashMap::new();
        for node in graph.keys() {
            in_degree.entry(node.clone()).or_insert(0);
            for neighbor in &graph[node] {
                *in_degree.entry(neighbor.clone()).or_insert(0) += 1;
            }
        }

        // Step 2: Collect nodes with in-degree 0
        let mut queue: VecDeque<String> = in_degree
            .iter()
            .filter(|(_, &degree)| degree == 0)
            .map(|(node, _)| node.clone())
            .collect();

        let mut sorted = Vec::new();

        // Step 3: Process the queue
        while let Some(node) = queue.pop_front() {
            sorted.push(node.clone());

            if let Some(neighbors) = graph.get(&node) {
                for neighbor in neighbors {
                    if let Some(degree) = in_degree.get_mut(neighbor) {
                        *degree -= 1;
                        if *degree == 0 {
                            queue.push_back(neighbor.clone());
                        }
                    }
                }
            }
        }

        // Step 4: Check for cycles
        if sorted.len() == graph.len() {
            Ok(sorted)
        } else {
            Err("Graph contains a cycle!".to_string())
        }
    }

    pub fn populate_inherited_vars_methods(&mut self) {
        // Build inheritance graph mapping class_name -> [child_class_name*]
        if self.inheritance_graph.is_some() {
            return;
        }

        self.inheritance_graph = Some(HashMap::new());
        self.build_inheritance_graph();

        // Populate inherited fields and methods; children inherit all instance variables from their parent classes
        // and all methods from their parent classes, unless they override them

        if let Ok(topological_order) =
            Program::topological_sort_inheritance_graph(self.inheritance_graph.as_ref().unwrap())
        {
            for class_name in &topological_order {
                // Propagate instance variables to children
                let class_children = self
                    .inheritance_graph
                    .as_ref()
                    .unwrap()
                    .get(class_name)
                    .expect("Class not found in inheritance graph");

                for child_name in class_children {
                    if let Some(mut child) = self.classes.remove(child_name) {
                        if class_name != BASE_CLASS_NAME {
                            let parent = self
                                .classes
                                .get(class_name)
                                .expect("Parent class not found in classes");

                            // Propagate fields to children, check for duplicated
                            if parent.field_types.iter().any(|(field_name, _)| {
                                if child.field_types.iter().any(|(name, _)| name == field_name) {
                                    true
                                } else {
                                    false
                                }
                            }) {
                                panic!("Invalid program: child class {child_name} has a field which is duplicated from parent class {class_name}");
                            }

                            child.field_types.splice(0..0, parent.field_types.clone());

                            // Propagate methods to child from parent
                            for (method_name, (idx, owner_name)) in &parent.vtable_indices {
                                if child.methods.iter().all(|(name, _)| name != method_name) {
                                    // If this is a class from the parent which the child does not override, add it to the child
                                    child.vtable_indices.insert(
                                        method_name.clone(),
                                        (idx.clone(), owner_name.clone()),
                                    );
                                } else {
                                    // Otherwise, the child has overriden the method and becomes its owner
                                    child.vtable_indices.insert(
                                        method_name.clone(),
                                        (idx.clone(), child_name.clone()),
                                    );
                                }
                            }
                        }

                        // Finish vtable indices for children if they have methods which are not in the parent
                        for method_name in child.methods.keys() {
                            let n_methods = child.vtable_indices.len();

                            child
                                .vtable_indices
                                .entry(method_name.clone())
                                .or_insert((n_methods, child.name.clone()));
                        }

                        self.classes.insert(child_name.clone(), child);
                    }
                }
            }
        } else {
            panic!("Invalid program: inheritance graph contains a cycle");
        }
    }

    fn class_a_inherits_from_b(&self, class_a: &String, class_b: &String) -> bool {
        if class_a == class_b {
            return true;
        } else {
            let child_classes = self
                .inheritance_graph
                .as_ref()
                .expect("Inheritance graph has yet to be created")
                .get(class_b)
                .expect("Class {class_b} not found in inheritance graph");

            for child_class in child_classes {
                if self.class_a_inherits_from_b(class_a, child_class) {
                    return true;
                }
            }
        }

        false
    }

    pub fn expr_a_subtypes_b(&self, a: &ExprType, b: &ExprType) -> bool {
        match (a, b) {
            (ExprType::NullPtr, ExprType::RecordPointer(_)) => true,
            (ExprType::NullPtr, ExprType::ObjectPointer(_)) => true,
            (ExprType::RecordPointer(_), ExprType::NullPtr) => true,
            (ExprType::ObjectPointer(_), ExprType::NullPtr) => true,
            (ExprType::RecordPointer(e), ExprType::RecordPointer(t)) => e == t,
            (ExprType::ObjectPointer(class_a), ExprType::ObjectPointer(class_b)) => {
                self.class_a_inherits_from_b(&class_a, &class_b)
            }
            _ => a == b,
        }
    }
}

pub struct CompileCtx<'a> {
    pub scope: VariableScope,
    pub rbp_offset: i32,
    pub rbx_offset: i32,
    pub tag_id: i32,
    pub instr_vec: Vec<Instr<'a>>,
}

impl<'a> CompileCtx<'a> {
    pub fn new() -> CompileCtx<'a> {
        CompileCtx {
            scope: HashMap::new(),
            rbp_offset: 0,
            rbx_offset: 0,
            tag_id: 0,
            instr_vec: Vec::new(),
        }
    }

    pub fn incr_tag_id(&mut self) -> i32 {
        self.tag_id += 1;
        self.tag_id
    }

    pub fn clear_instrs(&mut self) {
        self.instr_vec.clear();
    }

    pub fn clear_scope(&mut self) {
        self.scope.clear();
    }

    pub fn reset_rbx_offset(&mut self, offset: i32) {
        self.rbx_offset = offset;
    }

    pub fn reset_rbp_offset(&mut self, offset: i32) {
        self.rbp_offset = offset;
    }

    /// Push the value of a register to the stack at the given offset from RBP and return the new offset
    pub fn push_reg_to_stack(&mut self, reg: Reg) -> i32 {
        let new_rbp_offset = self.rbp_offset - SIZE_OF_DWORD;

        self.instr_vec.push(Instr::IMov(
            Val::RegOffset(Reg::RBP, new_rbp_offset),
            Val::Reg(reg),
        ));

        self.rbp_offset = new_rbp_offset;
        new_rbp_offset
    }

    /// Push an immediate value to the stack at the given offset from RBP and return the new offset
    pub fn push_val_to_stack(&mut self, val: i32) -> i32 {
        let new_rbp_offset = self.rbp_offset - SIZE_OF_DWORD;

        self.instr_vec.push(Instr::IMov(
            Val::RegOffset(Reg::RBP, new_rbp_offset),
            Val::Imm(val),
        ));

        self.rbp_offset = new_rbp_offset;
        new_rbp_offset
    }

    /// Push RBX to the RBX mini-stack at the given offset from RBP and return the new offset
    pub fn push_rbx_to_stack(&mut self) -> i32 {
        let new_rbx_offset = self.rbx_offset - SIZE_OF_DWORD;

        self.instr_vec.push(Instr::IMov(
            Val::RegOffset(Reg::RBP, new_rbx_offset),
            Val::Reg(Reg::RBX),
        ));

        self.rbx_offset = new_rbx_offset;
        new_rbx_offset
    }

    /// Pop RBX from the RBX mini-stack at the given offset from RBP and return the new offset
    pub fn pop_rbx_from_ministack(&mut self) -> i32 {
        let new_rbx_offset = self.rbx_offset + SIZE_OF_DWORD;

        self.instr_vec.push(Instr::IMov(
            Val::Reg(Reg::RBX),
            Val::RegOffset(Reg::RBP, self.rbx_offset),
        ));

        self.rbx_offset = new_rbx_offset;
        new_rbx_offset
    }

    /// Set the carry forward assignment value in RBX to the given value
    pub fn set_carry_forward(&mut self, val: bool) {
        self.instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(i32::from(val))));
    }

    /// Push RBX to the stack and set the carry forward assignment value in RBX to the given value
    pub fn push_rbx_and_set_carry_forward(&mut self, val: bool) -> i32 {
        let new_rbx_offset = self.push_rbx_to_stack();
        self.set_carry_forward(val);

        new_rbx_offset
    }
}
