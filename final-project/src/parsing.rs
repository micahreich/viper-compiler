use core::panic;
use std::collections::{HashMap, HashSet};
// use prettydiff::format_table::new;
use crate::utils::{self, format_method_name_label, is_valid_identifier};
use sexp::Atom::*;
use sexp::*;

use crate::types::*;

pub fn parse_let_expr(b_vec_sexp: &Sexp, expr_sexp: &Sexp, symbol_table: &SymbolTable) -> Expr {
    match b_vec_sexp {
        Sexp::List(vec) => {
            let bindings_vector = vec.iter().map(|sexp_list| {
                match sexp_list {
                    Sexp::List(vec) => match &vec[..] {
                        [Sexp::Atom(S(identifier)), e] => {
                            if !is_valid_identifier(identifier) {
                                panic!("Reserved keyword or invalid identifier used as variable name in let expression: {identifier}");
                            }

                            (identifier.clone(), parse_expr(e, symbol_table))
                        }
                        _ => {
                            panic!("Invalid let expression: bindings must be of the form (<identifier> <expr>)")
                        },
                    },
                    _ => {
                        panic!("Invalid let expression: bindings must be of the form (<identifier> <expr>)")
                    },
                }
            })
            .collect::<Vec<(String, Expr)>>();

            Expr::Let(
                bindings_vector,
                Box::new(parse_expr(expr_sexp, symbol_table)),
            )
        }
        _ => panic!("Invalid program: malformed let expression (are you missing parens?)"),
    }
}

pub fn parse_block_expr(e_vec_sexp: &[Sexp], symbol_table: &SymbolTable) -> Expr {
    let expression_vec = e_vec_sexp
        .iter()
        .map(|e| parse_expr(e, symbol_table))
        .collect::<Vec<Expr>>();

    if expression_vec.len() == 0 {
        panic!("Invalid program: blocks must have at least one expression");
    }

    Expr::Block(expression_vec)
}

pub fn parse_expr(s: &Sexp, symbol_table: &SymbolTable) -> Expr {
    match s {
        Sexp::Atom(Atom::F(_)) => panic!("Invalid program: floats are not supported"),
        Sexp::Atom(Atom::S(id)) => {
            if id == "true" {
                Expr::Boolean(true)
            } else if id == "false" {
                Expr::Boolean(false)
            } else {
                Expr::Id(id.to_string())
            }
        }
        Sexp::Atom(Atom::I(x)) => match i32::try_from(*x) {
            Ok(val) => Expr::Number(val),
            Err(_) => panic!("Cannot convert int literal to i32"),
        },
        Sexp::List(vec) => match &vec[..] {
            [Sexp::Atom(S(op)), e] if op == "add1" => {
                Expr::UnOp(Op1::Add1, Box::new(parse_expr(e, symbol_table)))
            }
            [Sexp::Atom(S(op)), e] if op == "sub1" => {
                Expr::UnOp(Op1::Sub1, Box::new(parse_expr(e, symbol_table)))
            }
            [Sexp::Atom(S(op)), e] if op == "print" => {
                // Parse a print expression as let x = eval e in print e end
                Expr::Let(
                    vec![("__tmp".into(), parse_expr(e, symbol_table))],
                    Box::new(Expr::UnOp(Op1::Print, Box::new(Expr::Id("__tmp".into())))),
                )
            }
            [Sexp::Atom(S(op)), e1, Sexp::Atom(S(field))] if op == "lookup" => {
                // We parse a lookup expression as let x = eval e in lookup x field end
                // This is done to avoid GC errors when the record is created inside the lookup expr
                Expr::Let(
                    vec![("__tmp".into(), parse_expr(e1, symbol_table))],
                    Box::new(Expr::Lookup(
                        Box::new(Expr::Id("__tmp".into())),
                        field.clone(),
                    )),
                )
            }
            [Sexp::Atom(S(op)), e1, e2] if op == "+" => Expr::BinOp(
                Op2::Plus,
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "-" => Expr::BinOp(
                Op2::Minus,
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "*" => Expr::BinOp(
                Op2::Times,
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "<" => Expr::BinOp(
                Op2::Less,
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "<=" => Expr::BinOp(
                Op2::LessEqual,
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == ">" => Expr::BinOp(
                Op2::Greater,
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == ">=" => Expr::BinOp(
                Op2::GreaterEqual,
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "=" => Expr::BinOp(
                Op2::Equal,
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
            ),
            [Sexp::Atom(S(op)), b_vec, e] if op == "let" => parse_let_expr(b_vec, e, symbol_table),
            [Sexp::Atom(S(op)), Sexp::Atom(S(name)), e1] if op == "set!" => {
                Expr::Set(name.clone(), Box::new(parse_expr(e1, symbol_table)))
            }
            [Sexp::Atom(S(op)), Sexp::Atom(S(record_name)), Sexp::Atom(S(field_name)), e1]
                if op == "set!" =>
            {
                Expr::SetField(
                    record_name.clone(),
                    field_name.clone(),
                    Box::new(parse_expr(e1, symbol_table)),
                )
            }
            [Sexp::Atom(S(op)), e1, e2, e3] if op == "if" => Expr::If(
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
                Box::new(parse_expr(e3, symbol_table)),
            ),
            [Sexp::Atom(S(op)), e1, e2] if op == "repeat-until" => Expr::RepeatUntil(
                Box::new(parse_expr(e1, symbol_table)),
                Box::new(parse_expr(e2, symbol_table)),
            ),
            _ => match &vec[0] {
                Sexp::Atom(S(op)) if op == "block" => parse_block_expr(&vec[1..], symbol_table),
                Sexp::Atom(S(val)) if val == "true" => Expr::Boolean(true),
                Sexp::Atom(S(val)) if val == "false" => Expr::Boolean(false),
                Sexp::Atom(S(val)) if val == "call" => {
                    // Parse method calls as let __tmp = eval e1 in __tmp.method_name(e2, e3, ...) end
                    // With additional `self` / object pointer as first argument
                    if let Sexp::Atom(S(method_name)) = &vec[2] {
                        let args: Vec<Expr> = vec![Expr::Id("__tmp".into())]
                            .into_iter()
                            .chain(vec.iter().skip(3).map(|e| parse_expr(e, symbol_table)))
                            .collect();

                        Expr::Let(
                            vec![("__tmp".into(), parse_expr(&vec[1], symbol_table))],
                            Box::new(Expr::CallMethod("__tmp".into(), method_name.clone(), args)),
                        )
                    } else {
                        panic!("Method names must be provided at compile time when calling")
                    }
                }
                Sexp::Atom(S(name)) => {
                    let mut args = Vec::new();

                    vec.iter().skip(1).for_each(|e| {
                        args.push(parse_expr(e, symbol_table));
                    });

                    match symbol_table.get(name) {
                        Some(SymbolType::Function(_)) => Expr::Call(name.clone(), args),
                        Some(SymbolType::Record(_)) => Expr::RecordInitializer(name.clone(), args),
                        Some(SymbolType::Class(_)) => Expr::ObjectInitializer(name.clone(), args),
                        None => panic!(
                            "Invalid program: function call, record initialization, or class initialization for undefined symbol: {}",
                            name
                        ),
                    }
                }
                _ => panic!("Invalid program: malformed expression"),
            },
        },
    }
}

pub fn parse_argument(s: &Sexp, symbol_table: &SymbolTable) -> (String, ExprType) {
    let err_msg = "Malformed argument, expecting argument of form (name type)";

    match s {
        Sexp::Atom(_) => panic!("{}", err_msg),
        Sexp::List(vec) => {
            if vec.len() != 2 {
                panic!("{}", err_msg)
            }

            match (&vec[0], &vec[1]) {
                (Sexp::Atom(S(name)), Sexp::Atom(S(type_name))) => {
                    if !is_valid_identifier(name) {
                        panic!("Reserved keyword or invalid identifier used as variable name in function argument: {name}");
                    }

                    (
                        name.clone(),
                        ExprType::from_stringified_type(type_name, symbol_table),
                    )
                }
                _ => panic!("{}", err_msg),
            }
        }
    }
}

pub fn parse_record_defn(s: &Sexp, symbol_table: &SymbolTable) -> Record {
    let err_msg = "Malformed record definition, expecting definition of form (record record_name (field1 type1) (field2 type2) ...)";

    match s {
        Sexp::Atom(_) => panic!("Malformed definition"),
        Sexp::List(vec) => {
            if vec.len() != 3 {
                panic!("{}", err_msg);
            }

            match (&vec[0], &vec[1], &vec[2]) {
                (Sexp::Atom(S(keyword)), Sexp::Atom(S(record_name)), Sexp::List(arg_vec)) => {
                    if keyword != "record" {
                        panic!("Malformed record definition, expecting record definition with keyword `record`");
                    }

                    let record_fields = arg_vec
                        .iter()
                        .map(|s1| parse_argument(s1, symbol_table))
                        .collect::<Vec<(String, ExprType)>>();

                    Record {
                        name: record_name.clone(),
                        field_types: record_fields,
                    }
                }
                _ => panic!("{}", err_msg),
            }
        }
    }
}

pub fn parse_class_defn(s: &Sexp, symbol_table: &SymbolTable) -> Class {
    let err_msg = "Malformed class definition, expecting definition of form \
    (class class_name inherits_name
        (instance_vars (arg1 type1) (arg2 type2) ...)
        (method_list
            (fun method_name (arg1 type1) (arg2 type2) ... return_type
                body_expr
            )
            ...
        )
    )";

    match s {
        Sexp::Atom(_) => panic!("{}", err_msg),
        Sexp::List(vec) => {
            match (&vec[0], &vec[1], &vec[2], &vec[3], &vec[4]) {
                (
                    Sexp::Atom(S(keyword)),
                    Sexp::Atom(S(class_name)),
                    Sexp::Atom(S(inherits_name)),
                    Sexp::List(instance_var_vec),
                    Sexp::List(methods_vec),
                ) => {
                    if keyword != "class" {
                        panic!("Malformed class definition, expecting class definition with keyword `class`");
                    }

                    let instance_vars = match instance_var_vec.as_slice() {
                        [Sexp::Atom(S(keyword)), instance_var_vec @ ..] => {
                            if keyword != "instance_vars" {
                                panic!("Malformed definition: expecting instance variable list after class name with label `instance_vars`");
                            }

                            instance_var_vec
                                .iter()
                                .map(|s1| parse_argument(s1, symbol_table))
                                .collect::<Vec<(String, ExprType)>>()
                        }
                        _ => panic!("{}", err_msg),
                    };

                    let mut methods = HashMap::new();

                    match methods_vec.as_slice() {
                        [Sexp::Atom(S(keyword)), methods_vec @ ..] => {
                            if keyword != "method_list" {
                                panic!("Malformed definition: expecting method list after instance variables with label `method_list`");
                            }

                            methods_vec.iter().for_each(|s1| {
                                let mut func = parse_func_defn(s1, symbol_table);
                                let method_name_unmangled = func.name.clone();

                                // Add the implicit `self` first argument to the signature
                                func.arg_types.insert(0,("self".to_string(), ExprType::ObjectPointer(class_name.clone())));

                                // Add the class name prefix to the name part of the signature
                                func.name = utils::format_method_name_label(&class_name, &func.name);

                                if methods.insert(
                                    method_name_unmangled.clone(),
                                    func,
                                ).is_some() {
                                    panic!("Duplicate method definition: {method_name_unmangled} in class {class_name}");
                                }
                            });
                        }
                        _ => panic!("{}", err_msg),
                    }

                    Class::new(
                        class_name.clone(),
                        inherits_name.clone(),
                        instance_vars,
                        methods,
                    )
                }
                _ => panic!("{}", err_msg),
            }
        }
    }
}

pub fn parse_func_defn(s: &Sexp, symbol_table: &SymbolTable) -> Function {
    let err_msg = "Malformed function definition, expecting definition of form\
    (fun function_name (arg1 type1) (arg2 type2) ... return_type
        body_expr
    )";

    match s {
        Sexp::Atom(_) => panic!("{}", err_msg),
        Sexp::List(vec) => match (&vec[0], &vec[1], &vec[2]) {
            (Sexp::Atom(S(keyword)), Sexp::Atom(S(func_name)), Sexp::List(arg_vec)) => {
                if keyword != "fun" {
                    panic!("Malformed function definition, expecting function definition with keyword `fun`");
                }

                let func_args = arg_vec
                    .iter()
                    .map(|s1| parse_argument(s1, symbol_table))
                    .collect::<Vec<(String, ExprType)>>();

                if let Sexp::Atom(S(return_type)) = &vec[vec.len() - 2] {
                    let func_return_type =
                        ExprType::from_stringified_type(return_type, symbol_table);
                    let func_body_expr = parse_expr(&vec[vec.len() - 1], symbol_table);

                    Function {
                        name: func_name.clone(),
                        arg_types: func_args,
                        return_type: func_return_type,
                        body: Box::new(func_body_expr),
                    }
                } else {
                    panic!("{}", err_msg);
                }
            }
            _ => panic!("{}", err_msg),
        },
    }
}

pub fn parse_prog(s: &Sexp) -> Program {
    let mut prog = Program::new();

    // Keep track of names so that we know what type of object we're instantiating, do 1
    // pass over the program to just get the names of all the records, functions, and classes
    let mut symbol_table = SymbolTable::new();

    if let Sexp::List(vec) = s {
        for s1 in vec {
            if let Sexp::List(sub_vec) = s1 {
                if sub_vec.len() == 0 {
                    panic!("Malformed program: empty expression");
                } else if sub_vec.len() < 2 {
                    continue;
                }

                match (&sub_vec[0], &sub_vec[1]) {
                    (Sexp::Atom(S(identifier)), Sexp::Atom(S(name))) => {
                        if let Some(s) = SymbolType::from_stringified_type(identifier, name) {
                            symbol_table.insert(name, s);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    // Go through the program parsing all function bodies, method bodies, and the main expression
    match s {
        Sexp::Atom(_) => panic!("Malformed program"),
        Sexp::List(vec) => {
            for s1 in vec {
                match s1 {
                    Sexp::Atom(_) => {
                        // This is when the main expression is just a value like a number or boolean
                        prog.set_main_expr(parse_expr(s1, &symbol_table));
                    }
                    Sexp::List(sub_vec) => match &sub_vec[0] {
                        Sexp::Atom(S(name)) => match name.as_str() {
                            "fun" => prog.add_function(parse_func_defn(s1, &symbol_table)),
                            "record" => prog.add_record(parse_record_defn(s1, &symbol_table)),
                            "class" => prog.add_class(parse_class_defn(s1, &symbol_table)),
                            _ => prog.set_main_expr(parse_expr(s1, &symbol_table)),
                        },
                        _ => panic!("Invalid program: malformed program"),
                    },
                }
            }
        }
    }

    // This step will populate each class's vtable map, which
    // stores an index for each method that it defines and inherits
    prog.populate_inherited_vars_methods();
    prog
}
