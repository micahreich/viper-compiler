use core::panic;
use im::{HashMap, HashSet};
// use prettydiff::format_table::new;
use sexp::Atom::*;
use sexp::*;

use crate::types::*;

pub fn format_method_name(class_name: &str, method_name: &str) -> String {
    format!("__{}_{}", class_name, method_name)
}

pub fn parse_let_expr(b_vec_sexp: &Sexp, expr_sexp: &Sexp, defns: &ProgDefns) -> Expr {
    match b_vec_sexp {
        Sexp::List(vec) => {
            let bindings_vector: Vec<(String, Expr)> = vec.iter().map(|sexp_list| {
                match sexp_list {
                    Sexp::List(vec) => match &vec[..] {
                        [Sexp::Atom(S(identifier)), e] => (identifier.clone(), parse_expr(e, defns)),
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

            Expr::Let(bindings_vector, Box::new(parse_expr(expr_sexp, defns)))
        }
        _ => panic!("Invalid program: malformed let expression (are you missing parens?)"),
    }
}

pub fn parse_block_expr(e_vec_sexp: &[Sexp], defns: &ProgDefns) -> Expr {
    let expression_vec: Vec<Expr> = e_vec_sexp.iter().map(|e| parse_expr(e, defns)).collect();

    if expression_vec.len() == 0 {
        panic!("Blocks must have at least one expression");
    }

    Expr::Block(expression_vec)
}

pub fn parse_expr(s: &Sexp, defns: &ProgDefns) -> Expr {
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
                Expr::UnOp(Op1::Add1, Box::new(parse_expr(e, defns)))
            }
            [Sexp::Atom(S(op)), e] if op == "sub1" => {
                Expr::UnOp(Op1::Sub1, Box::new(parse_expr(e, defns)))
            }
            [Sexp::Atom(S(op)), e] if op == "print" => {
                Expr::UnOp(Op1::Print, Box::new(parse_expr(e, defns)))
            }
            [Sexp::Atom(S(op)), e1, Sexp::Atom(S(field))] if op == "lookup" => {
                Expr::Lookup(Box::new(parse_expr(e1, defns)), field.clone())
            }
            [Sexp::Atom(S(op)), e1, e2] if op == "+" => Expr::BinOp(
                Op2::Plus,
                Box::new(parse_expr(e1, defns)),
                Box::new(parse_expr(e2, defns)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "-" => Expr::BinOp(
                Op2::Minus,
                Box::new(parse_expr(e1, defns)),
                Box::new(parse_expr(e2, defns)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "*" => Expr::BinOp(
                Op2::Times,
                Box::new(parse_expr(e1, defns)),
                Box::new(parse_expr(e2, defns)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "<" => Expr::BinOp(
                Op2::Less,
                Box::new(parse_expr(e1, defns)),
                Box::new(parse_expr(e2, defns)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "<=" => Expr::BinOp(
                Op2::LessEqual,
                Box::new(parse_expr(e1, defns)),
                Box::new(parse_expr(e2, defns)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == ">" => Expr::BinOp(
                Op2::Greater,
                Box::new(parse_expr(e1, defns)),
                Box::new(parse_expr(e2, defns)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == ">=" => Expr::BinOp(
                Op2::GreaterEqual,
                Box::new(parse_expr(e1, defns)),
                Box::new(parse_expr(e2, defns)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "=" => Expr::BinOp(
                Op2::Equal,
                Box::new(parse_expr(e1, defns)),
                Box::new(parse_expr(e2, defns)),
            ),
            [Sexp::Atom(S(op)), b_vec, e] if op == "let" => parse_let_expr(b_vec, e, defns),
            [Sexp::Atom(S(op)), Sexp::Atom(S(name)), e1] if op == "set!" => {
                Expr::Set(name.clone(), Box::new(parse_expr(e1, defns)))
            }
            [Sexp::Atom(S(op)), Sexp::Atom(S(record_name)), Sexp::Atom(S(field_name)), e1]
                if op == "set!" =>
            {
                Expr::SetField(
                    record_name.clone(),
                    field_name.clone(),
                    Box::new(parse_expr(e1, defns)),
                )
            }
            [Sexp::Atom(S(op)), e1, e2, e3] if op == "if" => Expr::If(
                Box::new(parse_expr(e1, defns)),
                Box::new(parse_expr(e2, defns)),
                Box::new(parse_expr(e3, defns)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "repeat-until" => {
                Expr::RepeatUntil(Box::new(parse_expr(e1, defns)), Box::new(parse_expr(e2, defns)))
            },
            _ => match &vec[0] {
                Sexp::Atom(S(op)) if op == "block" => parse_block_expr(&vec[1..], defns),
                Sexp::Atom(S(val)) if val == "true" => Expr::Boolean(true),
                Sexp::Atom(S(val)) if val == "false" => Expr::Boolean(false),
                Sexp::Atom(S(val)) if val == "call" => {
                    if let Expr::Id(func_name) = parse_expr(&vec[1], defns) {
                        let mut args: Vec<Expr> = Vec::new();
                        // call obj_name method_name arg1 arg2 arg3...

                        // Since the first argument to call is an object
                        // that can't be resolved during parsing, we postpone
                        // checking validity of the method call to the actually compiling step
                        vec.iter().skip(3).enumerate().for_each(|(i, e)| {
                            args.push(parse_expr(e, defns));
                        });
    
                        Expr::CallMethod(Box::new(parse_expr(&vec[0], defns)), func_name, args)
                    } else {
                        panic!("Method names must be provided at compile time when calling")
                    }
                },
                Sexp::Atom(S(name)) => {
                    let mut args: Vec<Expr> = Vec::new();

                    vec.iter().skip(1).enumerate().for_each(|(i, e)| {
                        args.push(parse_expr(e, defns));
                    });

                    if defns.function_names.contains(name) {
                        Expr::Call(name.clone(), args)
                    } else if defns.record_names.contains(name) {
                        Expr::RecordInitializer(name.clone(), args)
                    } else if defns.class_names.contains(name) {
                        Expr::ObjectInitializer(name.clone(), args)
                    } else {
                        panic!(
                            "Invalid program: function call, record initialization, or class initialization for undefined name: {}",
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

pub fn parse_record_defn(s: &Sexp) -> Record {
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

            Record {
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
                panic!("Malformed class definition: expecting class name after keyword `class`");
            };

            let inherits_name = if let Sexp::Atom(S(name)) = &vec[2] {
                name
            } else {
                panic!("Malformed class definition: expecting inherited class name after class name");
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

            // let mut method_signatures: HashMap<String, FunctionSignature> = HashMap::new();

            // if let Sexp::List(arg_vec) = &vec[4] {
            //     for s1 in arg_vec {
            //         let mut parsed_method_signature = parse_func_signature(s1);
            //         let method_name = parsed_method_signature.name.clone();

            //         // Add the implicit `self` first argument to the signature
            //         parsed_method_signature.arg_types.insert(0,("self".to_string(), ExprType::ObjectPointer(class_name.clone())));

            //         // Add the class name prefix to the name part of the signature
            //         parsed_method_signature.name = format!("__{}_{}", class_name, method_name);

            //         if method_signatures.insert(
            //             method_name.clone(),
            //             parsed_method_signature,
            //         ).is_some() {
            //             panic!("Duplicate method definition: {method_name} in class {class_name}");
            //         }
            //     }
            // } else {
            //     panic!("Malformed definition: expecting argument list after method name");
            // }

            ClassSignature {
                name: class_name.clone(),
                inherits: inherits_name.clone(),
                field_types: field_types,
            }
        }
    }
}

pub fn parse_class_defn(s: &Sexp, defns: &ProgDefns) -> Class {
    let signature = parse_class_signature(s);
    let methods = parse_class_methods(s, defns);

    Class {
        name: signature.name,
        inherits: signature.inherits,
        field_types: signature.field_types,
        vtable_indices: HashMap::new(),
        methods: methods,
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
    defns: &ProgDefns,
) -> Function {
    let signature = parse_func_signature(s);

    match s {
        Sexp::List(vec) => {
            let func_body_expr = parse_expr(&vec[vec.len() - 1], defns);

            Function {
                name: signature.name,
                arg_types: signature.arg_types,
                return_type: signature.return_type,
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

pub fn parse_class_methods(s: &Sexp, defns: &ProgDefns) -> HashMap<String, Function> {
    match s {
        Sexp::List(sub_vec) => {
            let class_name = match &sub_vec[1] {
                Sexp::Atom(S(name)) => name,
                _ => panic!("Malformed definition"),
            };

            match &sub_vec[4] {
                Sexp::List(func_vec) => {
                    let mut class_methods: HashMap<String, Function> = HashMap::new();

                    func_vec.iter().for_each(|s1| {
                        let mut func = parse_func_defn(s1, defns);
                        let method_name_unmangled = func.name.clone();

                        // Add the implicit `self` first argument to the signature
                        func.arg_types.insert(0,("self".to_string(), ExprType::ObjectPointer(class_name.clone())));

                        // Add the class name prefix to the name part of the signature
                        func.name = format_method_name(class_name, &func.name);

                        if class_methods.insert(
                            method_name_unmangled.clone(),
                            func,
                        ).is_some() {
                            panic!("Duplicate method definition: {method_name_unmangled} in class {class_name}");
                        }
                    });
                    

                    // for s1 in func_vec {
                    //     class_methods.insert(
                    //         class_signature.name.clone(),
                    //         parse_func_defn(s1)
                    //     );
                    // }

                    // return Class {
                    //     signature: ctx
                    //         .class_signatures
                    //         .get(class_name)
                    //         .expect("Class signature not found")
                    //         .clone(),
                    //     methods: class_methods,
                    // };

                    return class_methods;
                }
                _ => panic!("Malformed class definition"),
            };
        }
        _ => panic!("Malformed program"),
    }
}

pub fn create_inheritance_graph(classes_map: &HashMap<String, Class>) -> HashMap<String, Vec<String>> {
    let mut inheritance_graph: HashMap<String, Vec<String>> = HashMap::new();

    for class in classes_map.values() {
        if !inheritance_graph.contains_key(&class.inherits) {
            inheritance_graph.insert(class.inherits.clone(), Vec::new());
        }

        inheritance_graph
            .get_mut(&class.inherits)
            .unwrap()
            .push(class.name.clone());
    }

    inheritance_graph
}

pub fn resolve_vtable_indices(
    classes_map: &mut HashMap<String, Class>,
    inheritance_graph: &HashMap<String, Vec<String>>,
) {
    let mut vtable_visited: HashSet<String> = HashSet::new();
    let class_names = classes_map.keys().cloned().collect::<Vec<String>>();

    class_names.iter().for_each(|class_name| {
        let _ = resolve_vtable_indices_by_class(
            &class_name,
            &mut vtable_visited,
            inheritance_graph,
            classes_map,
        );
    });

    // // Clone :( the class names so that no borrowing occurs of class_signatures
    // let class_names: Vec<String> = classes_map.keys().cloned().collect();

    // for class in class_names.iter() {
    //     resolve_vtable_indices_by_class(
    //         &class,
    //         &mut vtable_visited,
    //         inheritance_graph,
    //         classes_map,
    //     );
    // }

    // for class in class_names.iter() {
    //     let signature = class_signatures.get(class).unwrap();
    //     println!("Vtable indices for class {}: {:?}", class, signature.vtable_indices);
    // }
}

fn resolve_vtable_indices_by_class (
    current_class_name: &String,
    visited: &mut HashSet<String>,
    inheritance_graph: &HashMap<String, Vec<String>>,
    classes_map: &mut HashMap<String, Class>,
) {
    // This method is a DFS over the inheritance graph to ensure
    // all parent vtable indices are populated before populating the child's indices
    // let current_class = classes_map
    //     .get(current_class_name)
    //     .expect("Class not found");

    // if we already computed this class' indices, we can just return
    if visited.contains(current_class_name) {
        return;
    }

    visited.insert(current_class_name.clone());

    // let class_signature = class_signatures
    //     .get(current_class)
    //     .expect("Class signature not found")
    //     .clone();
    
    // Resolve parent vtable indices first
    let current_class_inherits_name = classes_map
        .get(current_class_name)
        .expect("Class not found")
        .inherits
        .clone();

    if current_class_inherits_name != BASE_CLASS_NAME {
        resolve_vtable_indices_by_class(&current_class_inherits_name, visited, inheritance_graph, classes_map);

        // // Copy parent vtable indices to current class
        // for (method_name, index) in &class_signatures
        //     .get(&class_signature.inherits)
        //     .unwrap()
        //     .vtable_indices
        // {
        //     new_vtable_indices.insert(method_name.clone(), index.clone());
        // }

        let parent_vtable_indices = &classes_map
            .get(&current_class_inherits_name)
            .expect("Class not found")
            .vtable_indices;

        classes_map
            .get_mut(current_class_name)
            .expect("Class not found")
            .vtable_indices = parent_vtable_indices.clone();

    }

    /*
     * VTable indices are stored/defined as follows:
     * - Each parent function should map to the same vtable index as it did in the parent class
     *  (note this won't really work for multiple inheritance which we don't support)
     * - Each new function is mapped sequentially to a new index in the vtable
     */

    let current_class = classes_map
        .get_mut(current_class_name)
        .expect("Class not found");

    // let current_class_defined_methods = &classes_map
    //     .get(current_class_name)
    //     .expect("Class not found")
    //     .methods;

    // let current_class_vtable_indices = &mut classes_map
    //     .get_mut(current_class_name)
    //     .expect("Class not found")
    //     .vtable_indices;

    for method_name in current_class.methods.keys() {
        // let existing_vtable_entry = classes_map
        //     .get(current_class_name)
        //     .unwrap()
        //     .vtable_indices.get(method_name);

        if let Some((i, class_owner_name)) = current_class.vtable_indices.get(method_name) {
            current_class.vtable_indices.insert(method_name.clone(), (*i, class_owner_name.clone()));
        } else {
            let index = current_class.vtable_indices.len();
            current_class.vtable_indices.insert(method_name.clone(), (index, current_class_name.clone()));
        }

        // if new_vtable_indices.contains_key(method_name) {
        //     // We are overriding a function!
        //     let curr_value = new_vtable_indices.get(method_name).unwrap();
        //     new_vtable_indices.insert(method_name.clone(), (curr_value.0, current_class.clone()));
        // } else {
        //     let index = new_vtable_indices.len();
        //     new_vtable_indices.insert(method_name.clone(), (index, current_class.clone()));
        // }
    }

    // Overrite the class' vtable indices (did it this way due to borrowing weirdness)
    // current_class.vtable_indices = new_vtable_indices;

    // Recurse on the children to populate all the remaining indices
    if let Some(children) = inheritance_graph.get(current_class_name) {
        for child_class_name in children {
            resolve_vtable_indices_by_class(child_class_name, visited, inheritance_graph, classes_map);
        }
    }
}

pub fn parse_prog(s: &Sexp) -> Program {
    // First go through program looking for function, record definitions, class definitions to fill in signatures
    // let mut function_signatures: HashMap<String, FunctionSignature> = HashMap::new();
    // let mut record_signatures: HashMap<String, Record> = HashMap::new();
    // let mut class_signatures: HashMap<String, ClassSignature> = HashMap::new();

    // let mut func_signatures: HashMap<FunctionSignature> = Vec::new();
    // let mut record_signatures: Vec<RecordSignature> = Vec::new();
    // let mut class_signatures: Vec<ClassSignature> = Vec::new();

    // let mut parsed_func_signatures: HashSet<String> = HashSet::new();
    // let mut parsed_record_signatures: HashSet<String> = HashSet::new();
    // let mut parsed_class_signatures: HashSet<String> = HashSet::new();

    // if let Sexp::List(vec) = s {
    //     for s1 in vec {
    //         if let Sexp::List(sub_vec) = s1 {
    //             if sub_vec.len() == 0 {
    //                 panic!("Invalid: empty expression");
    //             }
    //             if let Sexp::Atom(S(name)) = &sub_vec[0] {
    //                 if name == "fun" {
    //                     let func_signature = parse_func_signature(s1);
    //                     if function_signatures
    //                         .insert(func_signature.name.clone(), func_signature.clone())
    //                         .is_some()
    //                     {
    //                         panic!("Duplicate function definition: {}", func_signature.name);
    //                     }
    //                 } else if name == "record" {
    //                     let record_signature = parse_record(s1);
    //                     if record_signatures
    //                         .insert(record_signature.name.clone(), record_signature.clone())
    //                         .is_some()
    //                     {
    //                         panic!("Duplicate record definition: {}", record_signature.name);
    //                     }
    //                 } else if name == "class" {
    //                     let class_signature = parse_class_signature(s1);

    //                     if class_signature.inherits != BASE_CLASS_NAME
    //                         && !class_signatures.contains_key(&class_signature.inherits)
    //                     {
    //                         panic!(
    //                             "Could not find inherited class: {}",
    //                             class_signature.inherits
    //                         );
    //                     }

    //                     if class_signatures
    //                         .insert(class_signature.name.clone(), class_signature.clone())
    //                         .is_some()
    //                     {
    //                         panic!("Duplicate class definition: {}", class_signature.name);
    //                     }
    //                 }
    //             }
    //         }
    //     }
    // }

    // // Build up program with parsed function bodies, class method bodies
    // let mut parse_ctx = ProgDefns {
    //     fn_signatures: function_signatures,
    //     record_signatures: record_signatures,
    //     class_signatures: class_signatures,
    // };

    let mut records: HashMap<String, Record> = HashMap::new();
    let mut functions: HashMap<String, Function> = HashMap::new();
    let mut classes: HashMap<String, Class> = HashMap::new();
    let mut main_expr: Option<Box<Expr>> = None;

    // Keep track of names so that we know what type of object we're instantiating, do 1
    // pass over the program to just get the names of all the records, functions, and classes
    let mut defns = ProgDefns {
        record_names: HashSet::new(),
        class_names: HashSet::new(),
        function_names: HashSet::new(),
    };

    if let Sexp::List(vec) = s {
        for s1 in vec {
            if let Sexp::List(sub_vec) = s1 {
                if sub_vec.len() == 0 {
                    panic!("Invalid: empty expression");
                } else if sub_vec.len() < 2 {
                    continue;
                }

                match (&sub_vec[0], &sub_vec[1]) {
                    (Sexp::Atom(S(identifier)), Sexp::Atom(S(name))) => {
                        match (identifier.as_str(), name.as_str()) {
                            ("record", record_name) => {
                                defns.record_names.insert(record_name.to_string());
                            }
                            ("fun", func_name) => {
                                defns.function_names.insert(func_name.to_string());
                            }
                            ("class", class_name) => {
                                defns.class_names.insert(class_name.to_string());
                            }
                            _ => (),
                        }
                    },
                    _ => (),
                }
            }
        }
    }

    match s {
        Sexp::Atom(_) => panic!("Malformed program"),
        Sexp::List(vec) => {
            for s1 in vec {
                match s1 {
                    Sexp::Atom(_) => {
                        // This is when the main expression is just a value like a number or boolean
                        main_expr = Some(Box::new(parse_expr(s1, &defns)));
                    }
                    Sexp::List(sub_vec) => match &sub_vec[0] {
                        Sexp::Atom(S(name)) if name == "fun" => {
                            let func = parse_func_defn(s1, &defns);
                            let name = func.name.clone();

                            if functions.insert(name.clone(), func).is_some() {
                                panic!("Duplicate function definition: {}", name);
                            }
                        }
                        Sexp::Atom(S(name)) if name == "record" => {
                            let record = parse_record_defn(s1);
                            let name = record.name.clone();

                            if records
                                .insert(name.clone(), record)
                                .is_some()
                            {
                                panic!("Duplicate record definition: {}", name);
                            }
                        }
                        Sexp::Atom(S(name)) if name == "class" => {
                            let class = parse_class_defn(s1, &defns);
                            let name = class.name.clone();

                            if classes
                                .insert(class.name.clone(), class)
                                .is_some()
                            {
                                panic!("Duplicate class definition: {}", name);
                            }
                        }
                        Sexp::Atom(_) => {
                            main_expr = Some(Box::new(parse_expr(s1, &defns)));
                        }
                        _ => panic!("Malformed program"),
                    },
                }
            }
        }
    }

    // This step will populate each class's vtable map, which
    // stores an index for each method that it defines and inherits
    let inheritance_graph = create_inheritance_graph(&classes);

    println!("inheritance_graph: {:?}", inheritance_graph);

    resolve_vtable_indices(&mut classes, &inheritance_graph);

    Program {
        functions: functions,
        classes: classes,
        records: records,
        main_expr: main_expr.expect("Main expression not found"),
        inheritance_graph: inheritance_graph,
    }
}