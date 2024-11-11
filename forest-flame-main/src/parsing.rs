use core::panic;
use im::HashMap;
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
    println!("parsing: {:?}", s);

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
                            panic!(
                                "Too few arguments when calling function: {}",
                                name
                            )
                        }

                        if vec.len() - 1 > func_signature.arg_types.len() {
                            panic!(
                                "Too many arguments when calling function: {}",
                                name
                            )
                        }
                        
                        for i in 0..func_signature.arg_types.len() {
                            args.push(parse_expr(&vec[i + 1], ctx));
                        }

                        Expr::Call(func_signature.clone(), args)
                    } else if let Some(record_signature) = ctx.record_signatures.get(name) {
                        let mut args: Vec<Expr> = Vec::new();

                        if vec.len() - 1 < record_signature.field_types.len() {
                            panic!(
                                "Too few arguments when initializing record: {}",
                                name
                            )
                        }

                        if vec.len() - 1 > record_signature.field_types.len() {
                            panic!(
                                "Too many arguments when initializing record: {}",
                                name
                            )
                        }

                        for i in 0..record_signature.field_types.len() {
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
        },
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

pub fn parse_defn(s: &Sexp, ctx: &ProgDefns) -> Function {
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
                signature: ctx.fn_signatures.get(func_name).unwrap().clone(),
                body: Box::new(func_body_expr),
            }
        }
        _ => panic!("Malformed program"),
    }
}

pub fn parse_prog(s: &Sexp) -> (Prog, ProgDefns) {
    // Prog is made up of a series of definitions (funcs) and an expression

    // First go through program looking for function, record definitions to fill in signatures
    let mut function_signatures: HashMap<String, FunctionSignature> = HashMap::new();
    let mut record_signatures: HashMap<String, RecordSignature> = HashMap::new();

    if let Sexp::List(vec) = s {
        for s1 in vec {
            if let Sexp::List(sub_vec) = s1 {
                if sub_vec.len() == 0 {
                    panic!("Invalid: empty expression");
                }
                if let Sexp::Atom(S(name)) = &sub_vec[0] {
                    if name == "fun" {
                        let signature = parse_func_signature(s1);

                        if function_signatures
                            .insert(signature.name.clone(), signature.clone())
                            .is_some()
                        {
                            panic!("Duplicate function definition: {}", signature.name);
                        }
                    } else if name == "record" {
                        println!("found a record definition");

                        let record_signature = parse_record_signature(s1);
                        if record_signatures
                            .insert(record_signature.name.clone(), record_signature.clone())
                            .is_some()
                        {
                            panic!("Duplicate record definition: {}", record_signature.name);
                        }
                    }
                }
            }
        }
    }

    println!("{:?}", record_signatures);

    let parse_ctx: ProgDefns = ProgDefns {
        fn_signatures: function_signatures,
        record_signatures: record_signatures,
    };

    let mut functions: Vec<Function> = Vec::new();

    match s {
        Sexp::Atom(_) => panic!("Malformed program"),
        Sexp::List(vec) => {
            for s1 in vec {
                match s1 {
                    Sexp::Atom(_) => {
                        functions.push(Function {
                            signature: FunctionSignature {
                                name: MAIN_FN_TAG.to_string(),
                                arg_types: Vec::new(),
                                return_type: ExprType::Main,
                            },
                            body: Box::new(parse_expr(s1, &parse_ctx)),
                        });

                        return (functions, parse_ctx);
                    }
                    Sexp::List(sub_vec) => match &sub_vec[0] {
                        Sexp::Atom(S(name)) if name == "fun" => {
                            functions.push(parse_defn(s1, &parse_ctx));
                        }
                        Sexp::Atom(S(name)) if name == "record" => {
                            println!("found a record definition, 2nd part");
                        }
                        Sexp::Atom(_) => {
                            functions.push(Function {
                                signature: FunctionSignature {
                                    name: MAIN_FN_TAG.to_string(),
                                    arg_types: Vec::new(),
                                    return_type: ExprType::Main,
                                },
                                body: Box::new(parse_expr(s1, &parse_ctx)),
                            });

                            return (functions, parse_ctx);
                        }
                        _ => panic!("Malformed program"),
                    },
                }
            }
        }
    }

    (functions, parse_ctx)
}
