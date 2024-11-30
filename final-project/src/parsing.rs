use core::panic;
use im::{HashMap, HashSet};
// use prettydiff::format_table::new;
use sexp::Atom::*;
use sexp::*;

use crate::types::*;

pub fn parse_let_expr(b_vec_sexp: &Sexp, expr_sexp: &Sexp, ctx: &ProgDefns) -> Expr {
    match b_vec_sexp {
        Sexp::List(vec) => {
            let bindings_vector: Vec<(String, Expr)> = vec.iter().map(|sexp_list| {
                match sexp_list {
                    Sexp::List(vec) => match &vec[..] {
                        [Sexp::Atom(S(identifier)), e] => (identifier.clone(), parse_expr(e, ctx)),
                        _ => {
                            println!("{:?}", vec);
                            panic!("Invalid let expression: bindings must be of the form (<identifier> <expr>)")
                        },
                    },
                    _ => {
                        println!("{:?}", sexp_list);
                        panic!("Invalid let expression: bindings must be of the form (<identifier> <expr>)")
                    },
                }
            })
            .collect();

            Expr::Let(bindings_vector, Box::new(parse_expr(expr_sexp, ctx)))
        }
        _ => panic!("Invalid program: malformed let expression (are you missing parens?)"),
    }
}

pub fn parse_block_expr(e_vec_sexp: &[Sexp], ctx: &ProgDefns) -> Expr {
    let expression_vec: Vec<Expr> = e_vec_sexp.iter().map(|e| parse_expr(e, ctx)).collect();

    if expression_vec.len() == 0 {
        panic!("Blocks must have at least one expression");
    }

    Expr::Block(expression_vec)
}

pub fn parse_expr(s: &Sexp, ctx: &ProgDefns) -> Expr {
    match s {
        Sexp::Atom(Atom::F(_)) => panic!("Invalid program: floats are not allowed"),
        Sexp::Atom(Atom::S(str)) => {
            if str == "true" {
                Expr::Boolean(true)
            } else if str == "false" {
                Expr::Boolean(false)
            } else {
                Expr::Id(str.to_string())
            }
        }
        Sexp::Atom(Atom::I(x)) => match i32::try_from(*x) {
            Ok(val) => Expr::Number(val),
            Err(_) => panic!("Invalid number; cannot convert to i32"),
        },
        Sexp::List(vec) => match &vec[..] {
            [Sexp::Atom(S(op)), e] if op == "add1" => {
                Expr::UnOp(Op1::Add1, Box::new(parse_expr(e, ctx)))
            }
            [Sexp::Atom(S(op)), e] if op == "sub1" => {
                Expr::UnOp(Op1::Sub1, Box::new(parse_expr(e, ctx)))
            }
            [Sexp::Atom(S(op)), e] if op == "print" => {
                Expr::UnOp(Op1::Print, Box::new(parse_expr(e, ctx)))
            }
            [Sexp::Atom(S(op)), e1, Sexp::Atom(S(field))] if op == "lookup" => {
                Expr::Lookup(Box::new(parse_expr(e1, ctx)), field.clone())
            }
            [Sexp::Atom(S(op)), e1, e2] if op == "+" => Expr::BinOp(
                Op2::Plus,
                Box::new(parse_expr(e1, ctx)),
                Box::new(parse_expr(e2, ctx)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "-" => Expr::BinOp(
                Op2::Minus,
                Box::new(parse_expr(e1, ctx)),
                Box::new(parse_expr(e2, ctx)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "*" => Expr::BinOp(
                Op2::Times,
                Box::new(parse_expr(e1, ctx)),
                Box::new(parse_expr(e2, ctx)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "<" => Expr::BinOp(
                Op2::Less,
                Box::new(parse_expr(e1, ctx)),
                Box::new(parse_expr(e2, ctx)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "<=" => Expr::BinOp(
                Op2::LessEqual,
                Box::new(parse_expr(e1, ctx)),
                Box::new(parse_expr(e2, ctx)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == ">" => Expr::BinOp(
                Op2::Greater,
                Box::new(parse_expr(e1, ctx)),
                Box::new(parse_expr(e2, ctx)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == ">=" => Expr::BinOp(
                Op2::GreaterEqual,
                Box::new(parse_expr(e1, ctx)),
                Box::new(parse_expr(e2, ctx)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "=" => Expr::BinOp(
                Op2::Equal,
                Box::new(parse_expr(e1, ctx)),
                Box::new(parse_expr(e2, ctx)),
            ),
            [Sexp::Atom(S(op)), b_vec, e] if op == "let" => parse_let_expr(b_vec, e, ctx),
            [Sexp::Atom(S(op)), Sexp::Atom(S(name)), e1] if op == "set!" => {
                Expr::Set(name.clone(), Box::new(parse_expr(e1, ctx)))
            }
            [Sexp::Atom(S(op)), Sexp::Atom(S(record_name)), Sexp::Atom(S(field_name)), e1]
                if op == "set!" =>
            {
                Expr::RecordSetField(
                    record_name.clone(),
                    field_name.clone(),
                    Box::new(parse_expr(e1, ctx)),
                )
            }
            [Sexp::Atom(S(op)), e1, e2, e3] if op == "if" => Expr::If(
                Box::new(parse_expr(e1, ctx)),
                Box::new(parse_expr(e2, ctx)),
                Box::new(parse_expr(e3, ctx)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "repeat-until" => {
                Expr::RepeatUntil(Box::new(parse_expr(e1, ctx)), Box::new(parse_expr(e2, ctx)))
            }
            _ => match &vec[0] {
                Sexp::Atom(S(op)) if op == "block" => parse_block_expr(&vec[1..], ctx),
                Sexp::Atom(S(val)) if val == "true" => Expr::Boolean(true),
                Sexp::Atom(S(val)) if val == "false" => Expr::Boolean(false),
                Sexp::Atom(S(name)) => {
                    if let Some(func_signature) = ctx.fn_signatures.get(name) {
                        let mut args: Vec<Expr> = Vec::new();

                        if vec.len() - 1 < func_signature.arg_types.len() {
                            panic!("Too few arguments when calling function: {}", name)
                        }

                        if vec.len() - 1 > func_signature.arg_types.len() {
                            panic!("Too many arguments when calling function: {}", name)
                        }

                        for i in 0..func_signature.arg_types.len() {
                            args.push(parse_expr(&vec[i + 1], ctx));
                        }

                        Expr::Call(func_signature.clone(), args)
                    } else if let Some(record_signature) = ctx.record_signatures.get(name) {
                        let mut args: Vec<Expr> = Vec::new();

                        if vec.len() - 1 < record_signature.field_types.len() {
                            panic!("Too few arguments when initializing record: {}", name)
                        }

                        if vec.len() - 1 > record_signature.field_types.len() {
                            panic!("Too many arguments when initializing record: {}", name)
                        }

                        for i in 0..record_signature.field_types.len() {
                            args.push(parse_expr(&vec[i + 1], ctx));
                        }

                        Expr::RecordInitializer(name.clone(), args)
                    } else if let Some(class_signature) = ctx.class_signatures.get(name) {
                        let mut args: Vec<Expr> = Vec::new();

                        if vec.len() - 1 < class_signature.field_types.len() {
                            panic!("Too few arguments when initializing record: {}", name)
                        }

                        if vec.len() - 1 > class_signature.field_types.len() {
                            panic!("Too many arguments when initializing record: {}", name)
                        }

                        for i in 0..class_signature.field_types.len() {
                            args.push(parse_expr(&vec[i + 1], ctx));
                        }

                        Expr::RecordInitializer(name.clone(), args)
                    } else {
                        println!("{:?}", vec);
                        panic!(
                            "Invalid program: function call or record initialization to undefined: {}",
                            name
                        );
                    }
                }
                _ => panic!("Invalid program: malformed expression"),
            },
        },
    }
}

pub fn parse_type(s: &Sexp) -> ExprType {
    match s {
        Sexp::Atom(S(type_name)) => type_name.parse().unwrap(),
        _ => {
            println!("{}", s);
            panic!("Unexpected type")
        }
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

pub fn parse_record_signature(s: &Sexp) -> RecordSignature {
    match s {
        Sexp::Atom(_) => panic!("Malformed definition"),
        Sexp::List(vec) => {
            match &vec[0] {
                Sexp::Atom(S(name)) => {
                    if name != "record" {
                        panic!("Malformed record definition, expecting function definition with keyword `record`");
                    }
                }
                _ => panic!("Malformed definition"),
            }

            let record_name = if let Sexp::Atom(S(name)) = &vec[1] {
                name
            } else {
                panic!("Malformed definition")
            };

            let mut record_fields: Vec<(String, ExprType)> = Vec::new();

            if let Sexp::List(arg_vec) = &vec[2] {
                for s1 in arg_vec {
                    record_fields.push(parse_argument(s1));
                }
            } else {
                panic!("Malformed definition: expecting argument list after function name");
            }

            RecordSignature {
                name: record_name.to_string(),
                field_types: record_fields,
            }
        }
    }
}

pub fn parse_class_signature(s: &Sexp) -> ClassSignature {
    match s {
        Sexp::Atom(_) => panic!("Malformed class definition"),
        Sexp::List(vec) => {
            match &vec[0] {
                Sexp::Atom(S(name)) => {
                    if name != "class" {
                        panic!("Malformed class definition, expecting class definition with keyword `class`");
                    }
                }
                _ => panic!("Malformed definition"),
            }

            let class_name = if let Sexp::Atom(S(name)) = &vec[1] {
                name
            } else {
                panic!("Malformed class definition")
            };

            let inherits_name = if let Sexp::Atom(S(name)) = &vec[2] {
                name
            } else {
                panic!("Malformed class definition")
            };

            // TODO @dkrajews: make this support the case of having no instance variables and only methods

            let mut field_types: Vec<(String, ExprType)> = Vec::new();

            if let Sexp::List(arg_vec) = &vec[3] {
                for s1 in arg_vec {
                    field_types.push(parse_argument(s1));
                }
            } else {
                panic!("Malformed definition: expecting instance variable list after class name");
            }

            let mut method_signatures: HashMap<String, FunctionSignature> = HashMap::new();

            if let Sexp::List(arg_vec) = &vec[4] {
                for s1 in arg_vec {
                    let parsed_func_signature = parse_func_signature(s1);
                    if method_signatures.insert(
                        parsed_func_signature.name.clone(),
                        parsed_func_signature.clone(),
                    ).is_some() {
                        panic!("Duplicate method definition: {} in class {class_name}", parsed_func_signature.name);
                    }
                }
            } else {
                panic!("Malformed definition: expecting argument list after method name");
            }

            ClassSignature {
                name: class_name.clone(),
                inherits: inherits_name.clone(),
                field_types: field_types,
                method_signatures: method_signatures,
                vtable_indices: HashMap::new(),
            }
        }
    }
}

pub fn parse_func_signature(s: &Sexp) -> FunctionSignature {
    match s {
        Sexp::Atom(_) => panic!("Malformed definition"),
        Sexp::List(vec) => {
            match &vec[0] {
                Sexp::Atom(S(name)) => {
                    if name != "fun" {
                        panic!("Malformed function definition, expecting function definition with keyword `fun`");
                    }
                }
                _ => panic!("Malformed definition"),
            }

            let func_name = if let Sexp::Atom(S(name)) = &vec[1] {
                name
            } else {
                panic!("Malformed definition")
            };

            let func_type = parse_type(&vec[vec.len() - 2]);

            let mut func_args: Vec<(String, ExprType)> = Vec::new();

            if let Sexp::List(arg_vec) = &vec[2] {
                for s1 in arg_vec {
                    func_args.push(parse_argument(s1));
                }
            } else {
                panic!("Malformed definition: expecting argument list after function name");
            }

            FunctionSignature {
                name: func_name.to_string(),
                arg_types: func_args,
                return_type: func_type,
            }
        }
    }
}

pub fn parse_func_defn(
    s: &Sexp,
    ctx: &ProgDefns,
    fn_signatures: &HashMap<String, FunctionSignature>
) -> Function {
    // Right now this function only works for pasing functions, will need to update
    // if defintions ever contain more than functions

    match s {
        Sexp::List(sub_vec) => {
            let func_name = match &sub_vec[1] {
                Sexp::Atom(S(name)) => name,
                _ => panic!("Malformed definition"),
            };

            let func_body_expr = parse_expr(&sub_vec[sub_vec.len() - 1], ctx);

            Function {
                signature: fn_signatures.get(func_name).unwrap().clone(),
                body: Box::new(func_body_expr),
            }
        }
        _ => panic!("Malformed program"),
    }
}

// pub fn parse_method_defn(s: &Sexp, ctx: &ProgDefns, class_name: &str) -> Function {
//     // Right now this function only works for pasing functions, will need to update
//     // if defintions ever contain more than functions

//     match s {
//         Sexp::List(sub_vec) => {
//             let func_name = match &sub_vec[1] {
//                 Sexp::Atom(S(name)) => name,
//                 _ => panic!("Malformed definition"),
//             };

//             let func_body_expr = parse_expr(&sub_vec[sub_vec.len() - 1], ctx);

//             Function {
//                 signature: ctx
//                     .class_signatures
//                     .get(class_name)
//                     .expect("Signature for class {class_name} not found")
//                     .method_signatures
//                     .iter()
//                     .find(|m| m.name == *func_name)
//                     .expect("Method {func_name} not found for class {class_name}")
//                     .clone(),
//                 body: Box::new(func_body_expr),
//             }
//         }
//         _ => panic!("Malformed program"),
//     }
// }

pub fn parse_class_methods(s: &Sexp, ctx: &ProgDefns) -> Class {
    match s {
        Sexp::List(sub_vec) => {
            let class_name = match &sub_vec[1] {
                Sexp::Atom(S(name)) => name,
                _ => panic!("Malformed definition"),
            };

            match &sub_vec[4] {
                Sexp::List(func_vec) => {
                    let mut class_methods: HashMap<String, Function> = HashMap::new();

                    let class_signature = ctx
                        .class_signatures
                        .get(class_name)
                        .expect("Class signature not found");

                    for s1 in func_vec {
                        class_methods.insert(
                            class_signature.name.clone(),
                            parse_func_defn(s1, ctx, &class_signature.method_signatures)
                        );
                    }

                    Class {
                        signature: ctx
                            .class_signatures
                            .get(class_name)
                            .expect("Class signature not found")
                            .clone(),
                        methods: class_methods,
                    }
                }
                _ => panic!("Malformed class definition"),
            };
        }
        _ => panic!("Malformed program"),
    }

    panic!("Malformed program");
}

pub fn create_inheritance_graph(class_signatures: &HashMap<String, ClassSignature>) -> HashMap<String, Vec<String>> {
    let mut inheritance_graph: HashMap<String, Vec<String>> = HashMap::new();

    for (class_name, class_signature) in class_signatures {
        if !inheritance_graph.contains_key(&class_signature.inherits) {
            inheritance_graph.insert(class_signature.inherits.clone(), Vec::new());
        }

        inheritance_graph
            .get_mut(&class_signature.inherits)
            .unwrap()
            .push(class_signature.name.clone());
    }

    inheritance_graph
}

pub fn resolve_vtable_indices(
    class_signatures: &HashMap<String, ClassSignature>,
    inheritance_graph: &HashMap<String, Vec<String>>,
) {
    let mut vtable_visited: HashSet<String> = HashSet::new();

    class_signatures.keys().map(|class| {
        resolve_vtable_indices_by_class(
            class,
            &mut vtable_visited,
            inheritance_graph,
            class_signatures,
        );
    });
}

fn resolve_vtable_indices_by_class (
    current_class: &String,
    visited: &mut HashSet<String>,
    inheritance_graph: &HashMap<String, Vec<String>>,
    class_signatures: &HashMap<String, ClassSignature>,
) {
    if visited.contains(current_class) {
        return;
    }

    visited.insert(current_class.clone());

    let class_signature = class_signatures
        .get(current_class)
        .expect("Class signature not found")
        .clone();

    let mut new_vtable_indices: HashMap<String, (i32, String)> = HashMap::new();

    // Resolve parent vtable indices first
    if class_signature.inherits != BASE_CLASS_NAME {
        let parent_name = class_signature.inherits.clone();
        resolve_vtable_indices_by_class(&parent_name, visited, inheritance_graph, class_signatures);

        // Copy parent vtable indices to current class
        for (method_name, index) in class_signatures
            .get(&class_signature.inherits)
            .unwrap()
            .vtable_indices
        {
            new_vtable_indices.insert(method_name.clone(), index.clone());
        }
    }

    for (method_name, method) in &class_signature.method_signatures {
        if new_vtable_indices.contains_key(method_name) {
            // We are overriding a function!
            let curr_value = new_vtable_indices.get(method_name).unwrap();
            new_vtable_indices.insert(method_name.clone(), (curr_value.0, current_class.clone()));
        } else {
            let index = new_vtable_indices.len() as i32;
            new_vtable_indices.insert(method_name.clone(), (index, current_class.clone()));
        }
    }

    class_signatures
        .get_mut(current_class)
        .unwrap()
        .vtable_indices = new_vtable_indices;

    if let Some(children) = inheritance_graph.get(current_class) {
        for child in children {
            resolve_vtable_indices_by_class(child, visited, inheritance_graph, class_signatures);
        }
    }
}

pub fn parse_prog(s: &Sexp) -> Program {
    // First go through program looking for function, record definitions, class definitions to fill in signatures
    let mut function_signatures: HashMap<String, FunctionSignature> = HashMap::new();
    let mut record_signatures: HashMap<String, RecordSignature> = HashMap::new();
    let mut class_signatures: HashMap<String, ClassSignature> = HashMap::new();

    // let mut func_signatures: HashMap<FunctionSignature> = Vec::new();
    // let mut record_signatures: Vec<RecordSignature> = Vec::new();
    // let mut class_signatures: Vec<ClassSignature> = Vec::new();

    // let mut parsed_func_signatures: HashSet<String> = HashSet::new();
    // let mut parsed_record_signatures: HashSet<String> = HashSet::new();
    // let mut parsed_class_signatures: HashSet<String> = HashSet::new();

    if let Sexp::List(vec) = s {
        for s1 in vec {
            if let Sexp::List(sub_vec) = s1 {
                if sub_vec.len() == 0 {
                    panic!("Invalid: empty expression");
                }
                if let Sexp::Atom(S(name)) = &sub_vec[0] {
                    if name == "fun" {
                        let func_signature = parse_func_signature(s1);
                        if function_signatures
                            .insert(func_signature.name.clone(), func_signature.clone())
                            .is_some()
                        {
                            panic!("Duplicate function definition: {}", func_signature.name);
                        }
                    } else if name == "record" {
                        let record_signature = parse_record_signature(s1);
                        if record_signatures
                            .insert(record_signature.name.clone(), record_signature.clone())
                            .is_some()
                        {
                            panic!("Duplicate record definition: {}", record_signature.name);
                        }
                    } else if name == "class" {
                        let class_signature = parse_class_signature(s1);

                        if class_signature.inherits != BASE_CLASS_NAME
                            && !class_signatures.contains_key(&class_signature.inherits)
                        {
                            panic!(
                                "Could not find inherited class: {}",
                                class_signature.inherits
                            );
                        }

                        if class_signatures
                            .insert(class_signature.name.clone(), class_signature.clone())
                            .is_some()
                        {
                            panic!("Duplicate class definition: {}", class_signature.name);
                        }
                    }
                }
            }
        }
    }

    let inheritance_graph = create_inheritance_graph(&class_signatures);
    resolve_vtable_indices(&class_signatures, &inheritance_graph);

    // Build up program with parsed function bodies, class method bodies
    let mut parse_ctx = ProgDefns {
        fn_signatures: function_signatures,
        record_signatures: record_signatures,
        class_signatures: class_signatures,
    };

    let mut functions: HashMap<String, Function> = HashMap::new();
    let mut classes:HashMap<String, Class> = HashMap::new();
    let mut main_expr: Option<Box<Expr>> = None;

    match s {
        Sexp::Atom(_) => panic!("Malformed program"),
        Sexp::List(vec) => {
            for s1 in vec {
                match s1 {
                    Sexp::Atom(_) => {
                        // This is when the main expression is just a value like a number or boolean
                        main_expr = Some(Box::new(parse_expr(s1, &parse_ctx)));
                    }
                    Sexp::List(sub_vec) => match &sub_vec[0] {
                        Sexp::Atom(S(name)) if name == "fun" => {
                            let f = parse_func_defn(s1, &parse_ctx, &parse_ctx.fn_signatures);
                            functions.insert(f.signature.name.clone(), f);
                        }
                        Sexp::Atom(S(name)) if name == "record" => {}
                        Sexp::Atom(S(name)) if name == "class" => {
                            let c = parse_class_methods(s1, &parse_ctx);
                            classes.insert(c.signature.name.clone(), c);
                        }
                        Sexp::Atom(_) => {
                            main_expr = Some(Box::new(parse_expr(s1, &parse_ctx)));
                        }
                        _ => panic!("Malformed program"),
                    },
                }
            }
        }
    }

    Program {
        functions: functions,
        classes: classes,
        main_expr: main_expr.expect("Main expression not found"),
    }
}