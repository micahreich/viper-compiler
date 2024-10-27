use core::panic;
use std::collections::HashSet;

use crate::types::*;

pub struct CompileCtx {
    pub scope: VariableScope,
    pub rbp_offset: i32,
    pub tag_id: i32,
}

fn push_rax_to_stack(instr_vec: &mut Vec<Instr>, rbp_offset: i32) -> i32 {
    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RBP, rbp_offset - SIZE_OF_NUMBER),
        Val::Reg(Reg::RAX),
    ));
    // instr_vec.push(Instr::IPush(Val::Reg(Reg::RAX)));
    rbp_offset - SIZE_OF_NUMBER
}

fn compile_to_instrs(
    e: &Expr,
    scope: &mut VariableScope,
    instr_vec: &mut Vec<Instr>,
    rbp_offset: &mut i32,
    tag_id: &mut i32,
    defns: &ProgDefns,
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
        Expr::Id(s) => match scope.get(s) {
            Some((s_rbp_offset, e_type)) => {
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, *s_rbp_offset),
                ));

                e_type.clone()
            }
            None => {
                if s == "NULL" {
                    instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                    return ExprType::RecordNullPtr;
                } else {
                    panic!("Invalid: Unbound variable identifier {s}");
                }
            }
        },
        Expr::UnOp(op, e) => {
            let e_type: ExprType =
                compile_to_instrs(e, scope, instr_vec, rbp_offset, tag_id, defns);

            let e_rbp_offset = push_rax_to_stack(instr_vec, *rbp_offset);
            *rbp_offset = e_rbp_offset;

            match op {
                Op1::Print => {
                    instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RSI),
                        Val::Imm(e_type.to_type_flag()),
                    ));

                    // Move rsp to most recent stack-allocated local variable
                    instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
                    instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(*rbp_offset)));
                    instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

                    // Align rsp to 16 bytes
                    instr_vec.push(ALIGN_RSP_16_BYTES);

                    instr_vec.push(Instr::ICall("snek_print".to_string()));

                    // Print statements should evaluate to the given value
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RAX),
                        Val::RegOffset(Reg::RBP, e_rbp_offset),
                    ));
                }
                x => {
                    if e_type != ExprType::Number {
                        panic!("Invalid type for unary operation");
                    }
                    match x {
                        Op1::Add1 => instr_vec.push(Instr::IAdd(Val::Reg(Reg::RAX), Val::Imm(1))),
                        Op1::Sub1 => instr_vec.push(Instr::ISub(Val::Reg(Reg::RAX), Val::Imm(1))),
                        _ => unreachable!(),
                    }

                    instr_vec.push(Instr::IJumpOverflow("overflow_error".to_string()));
                }
            };

            e_type.clone()
        }
        Expr::BinOp(op, e1, e2) => {
            // Compile e2 first so that subtraction works nicely, leaves e1 in rax
            let e2_type = compile_to_instrs(e2, scope, instr_vec, rbp_offset, tag_id, defns);
            let rbp_offset_e2_eval = push_rax_to_stack(instr_vec, *rbp_offset);
            *rbp_offset = rbp_offset_e2_eval;

            let e1_type = compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id, defns); // e1 is in rax

            // Perform some type checking on the arguments
            if *op == Op2::Equal && e1_type != e2_type {
                panic!("Type mismatch in equality comparison");
            } else if (*op != Op2::Equal)
                && !(e1_type == ExprType::Number && e2_type == ExprType::Number)
            {
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
                            Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));
                        instr_vec.push(Instr::ICMovEqual(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::Less => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));
                        instr_vec.push(Instr::ICMovLess(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::LessEqual => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
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
                            Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));
                        instr_vec.push(Instr::ICMovGreater(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::GreaterEqual => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
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

                ExprType::Boolean
            } else if matches!(op, Op2::Plus | Op2::Minus | Op2::Times) {
                match op {
                    Op2::Plus => {
                        instr_vec.push(Instr::IAdd(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        ));
                    }
                    Op2::Minus => {
                        instr_vec.push(Instr::ISub(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        ));
                    }
                    Op2::Times => {
                        instr_vec.push(Instr::IMul(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        ));
                    }
                    _ => unreachable!(),
                }

                instr_vec.push(Instr::IJumpOverflow("overflow_error".to_string()));
                ExprType::Number
            } else {
                panic!("Invalid binary operation {:?}", op);
            }
        }
        Expr::Let(bindings, e) => {
            let original_scope = scope.clone();

            // Add the bindings from the scope
            let mut existing_identifiers: HashSet<String> = HashSet::new();

            for (var, var_e) in bindings {
                if var == "input" || !is_valid_identifier(var) {
                    panic!("Reserved keyword or invalid identifier used as variable name in let expression");
                }

                let var_e_type =
                    compile_to_instrs(var_e, scope, instr_vec, rbp_offset, tag_id, defns);
                *rbp_offset = push_rax_to_stack(instr_vec, *rbp_offset);

                if existing_identifiers.contains(var) {
                    panic!("Duplicate binding");
                } else {
                    existing_identifiers.insert(var.clone());
                    scope.insert(var.clone(), (*rbp_offset, var_e_type));
                }
            }

            // Compile the expression
            let e_type = compile_to_instrs(e, scope, instr_vec, rbp_offset, tag_id, defns);

            // Restore original scope after the let expression is finished
            *scope = original_scope;

            e_type
        }
        Expr::Set(id, e1) => {
            let e1_type = compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id, defns);
            let (id_offset, _) = scope.get(id).unwrap();

            instr_vec.push(Instr::IMov(
                Val::RegOffset(Reg::RBP, *id_offset),
                Val::Reg(Reg::RAX),
            ));

            e1_type
        }
        Expr::Block(expr_vec) => {
            let mut last_e_type = ExprType::Number;

            for e in expr_vec {
                last_e_type = compile_to_instrs(e, scope, instr_vec, rbp_offset, tag_id, defns);
            }

            last_e_type
        }
        Expr::If(e1, e2, e3) => {
            let curr_tag_id = *tag_id;

            *tag_id += 1;
            // Compile e1
            compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id, defns);

            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            // If e1 evaluates to false, go to e3
            instr_vec.push(Instr::IJumpEqual(format!("else{curr_tag_id}")));

            // Compile e2
            let return_type = compile_to_instrs(e2, scope, instr_vec, rbp_offset, tag_id, defns);
            instr_vec.push(Instr::IJump(format!("end{curr_tag_id}")));

            // Compile e3
            instr_vec.push(Instr::ITag(format!("else{curr_tag_id}")));

            compile_to_instrs(e3, scope, instr_vec, rbp_offset, tag_id, defns);

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
            let return_type = compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id, defns);
            let rbp_offset_return = push_rax_to_stack(instr_vec, *rbp_offset);
            *rbp_offset = rbp_offset_return;

            // Compile e2
            compile_to_instrs(e2, scope, instr_vec, rbp_offset, tag_id, defns);
            // If e2 returned false, keep going
            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            instr_vec.push(Instr::IJumpEqual(format!("loop{curr_tag_id}")));

            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, rbp_offset_return),
            ));

            instr_vec.push(Instr::ITag(format!("end{curr_tag_id}")));

            return_type
        }
        Expr::Call(func_sig, args) => {
            // Ensure 16-byte stack alignment prior to calling function
            // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Reg(Reg::RSP)));

            let prev_rbp_offset = *rbp_offset;

            let n_args = i32::try_from(args.len()).unwrap();
            let stack_space_to_align = round_up_to_next_multiple_of_16(n_args * SIZE_OF_NUMBER);

            // Evaluate all the function arguments
            let mut evaluated_args_rbp_offsets: Vec<i32> = Vec::new();

            for arg_expr in args {
                let _arg_type =
                    compile_to_instrs(arg_expr, scope, instr_vec, rbp_offset, tag_id, defns);
                let rbp_offset_arg = push_rax_to_stack(instr_vec, *rbp_offset);
                *rbp_offset = rbp_offset_arg;

                evaluated_args_rbp_offsets.push(rbp_offset_arg);
            }

            // Move rsp to most recent stack-allocated local variable
            instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
            instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(*rbp_offset)));
            instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

            // Align rsp to 16 bytes
            instr_vec.push(ALIGN_RSP_16_BYTES);

            // Reserve space on the stack for the arguments
            instr_vec.push(Instr::ISub(
                Val::Reg(Reg::RSP),
                Val::Imm(stack_space_to_align),
            ));

            // Put the arguments onto the stack in the correct order
            for (i, arg_rbp_offset) in evaluated_args_rbp_offsets.iter().enumerate() {
                let rsp_offset = i32::try_from(i).unwrap() * SIZE_OF_NUMBER; // positive offset from $rsp

                // Move the argument from the stack to a temp register
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::R11),
                    Val::RegOffset(Reg::RBP, *arg_rbp_offset),
                ));

                instr_vec.push(Instr::IMov(
                    Val::RegOffset(Reg::RSP, rsp_offset),
                    Val::Reg(Reg::R11),
                ));
            }

            // Call the function
            instr_vec.push(Instr::ICall(func_sig.name.clone()));

            // Restore the rbp_offset to before we allocated space for the arguments
            *rbp_offset = prev_rbp_offset;

            func_sig.return_type.clone()
        }
        // Expr::Alloc(record_signature) => {
        //     // Move rsp to most recent stack-allocated local variable
        //     instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
        //     instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(*rbp_offset)));
        //     instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

        //     // Align rsp to 16 bytes
        //     instr_vec.push(ALIGN_RSP_16_BYTES);

        //     // Call malloc
        //     let n_bytes = i32::try_from(record_signature.field_types.len() * SIZE_OF_NUMBER as usize).unwrap();
        //     instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(n_bytes)));
        //     instr_vec.push(Instr::ICall("malloc".to_string()));

        //     ExprType::RecordPointer(record_signature.name.clone())
        // },
        Expr::Lookup(e1, field) => {
            let e1_type = compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id, defns);

            if let ExprType::RecordPointer(record_name) = e1_type {
                let record_signature = defns.record_signatures.get(&record_name).unwrap();

                let field_index = record_signature
                    .field_types
                    .iter()
                    .position(|(field_name, _)| field_name == field);

                if let Some(idx) = field_index {
                    // The pointer to the record is stored in rax after evaluating e1
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RAX),
                        Val::RegOffset(Reg::RAX, i32::try_from(idx).unwrap() * SIZE_OF_NUMBER),
                    ));

                    record_signature.field_types[idx].1.clone()
                } else {
                    panic!(
                        "Invalid field lookup: field {} not found in record {}",
                        field, record_name
                    );
                }
            } else {
                panic!("Invalid lookup expression, must be a record pointer");
            }
        }
        Expr::RecordInitializer(record_name, fields) => {
            // Move rsp to most recent stack-allocated local variable
            instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
            instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(*rbp_offset)));
            instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

            // Align rsp to 16 bytes
            instr_vec.push(ALIGN_RSP_16_BYTES);

            // Call malloc
            if let Some(record_signature) = defns.record_signatures.get(record_name) {
                let n_bytes =
                    i32::try_from(record_signature.field_types.len() * SIZE_OF_NUMBER as usize)
                        .unwrap();
                instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(n_bytes)));
                instr_vec.push(Instr::ICall("malloc".to_string()));

                // Move rax into temporary stack place
                let rbp_offset_ptr_eval = push_rax_to_stack(instr_vec, *rbp_offset);
                *rbp_offset = rbp_offset_ptr_eval;
                
                // Initialize the rest of the fields
                for (i, field_expr) in fields.iter().enumerate() {
                    let field_type_eval =
                        compile_to_instrs(field_expr, scope, instr_vec, rbp_offset, tag_id, defns);

                    if field_type_eval != ExprType::RecordNullPtr
                        && field_type_eval != record_signature.field_types[i].1
                    {
                        panic!("Type mismatch in record initializer: ensure field type matches expression type, expected {:?} but got {:?}", record_signature.field_types[i].1, field_type_eval);
                    }

                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::R11),
                        Val::RegOffset(Reg::RBP, rbp_offset_ptr_eval),
                    ));

                    instr_vec.push(Instr::IMov(
                        Val::RegOffset(Reg::R11, i32::try_from(i).unwrap() * SIZE_OF_NUMBER),
                        Val::Reg(Reg::RAX),
                    ));
                }

                // Move the record pointer back into rax
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, rbp_offset_ptr_eval),
                ));

                ExprType::RecordPointer(record_signature.name.clone())
            } else {
                panic!(
                    "Invalid record initializer: record {} not found in definitions",
                    record_name
                );
            }
        }
        // Expr::SetField(expr, _, expr1) => todo!(),
        // Expr::SetField(e1, field, e2) => {
        //     let e2_type = compile_to_instrs(e2, scope, instr_vec, rbp_offset, tag_id, defns);
        //     let rbp_offset_e2_eval = push_rax_to_stack(instr_vec, *rbp_offset);
        //     *rbp_offset = rbp_offset_e2_eval;

        //     let e1_type = compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id, defns);

        //     if let ExprType::RecordPointer(record_name) = e1_type {
        //         let record_signature = defns.record_signatures.get(&record_name).unwrap();

        //         let field_index = record_signature
        //             .field_types
        //             .iter()
        //             .position(|(field_name, _)| field_name == field);

        //         if let Some(idx) = field_index {
        //             // Make sure e2 has the same type as the field we are setting
        //             if e2_type != record_signature.field_types[idx].1 {
        //                 panic!("Type mismatch in set-field expression: ensure field type matches expression type");
        //             }

        //             // Move the new value into r11 temporary register
        //             instr_vec.push(Instr::IMov(
        //                 Val::Reg(Reg::R11),
        //                 Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
        //             ));

        //             // The pointer to the record is stored in rax after evaluating e1
        //             instr_vec.push(Instr::IMov(
        //                 Val::RegOffset(Reg::RAX, i32::try_from(idx).unwrap() * SIZE_OF_NUMBER),
        //                 Val::Reg(Reg::R11),
        //             ));

        //             e2_type
        //         } else {
        //             panic!("Invalid field set: field {} not found in record {}", field, record_name);
        //         }
        //     } else {
        //         panic!("Invalid set-field expression, must be a record pointer");
        //     }
        // },
    }
}

fn compile_instrs_to_str(instr_vec: &[Instr]) -> String {
    let n_spaces_indentation = 2;

    instr_vec
        .iter()
        .map(instr_to_str)
        .map(|s| format!("{}{}", " ".repeat(n_spaces_indentation), s))
        .collect::<Vec<String>>()
        .join("\n")
}

fn instr_to_str(i: &Instr) -> String {
    match i {
        Instr::IMov(dst, src) => {
            let size_specifier = if let Val::Imm(_) = src { "qword " } else { "" };
            format!(
                "mov {size_specifier}{}, {}",
                val_to_str(dst),
                val_to_str(src)
            )
        }
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
        Instr::IAnd(v1, v2) => format!("and {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::IPush(v) => format!("push {}", val_to_str(v)),
        Instr::IPop(v) => format!("pop {}", val_to_str(v)),
        Instr::IRet => "ret".to_string(),
        Instr::IComment(s) => format!("; {}", s),
    }
}

fn reg_to_str(r: &Reg) -> String {
    match r {
        Reg::RAX => "rax".to_string(),
        Reg::RSP => "rsp".to_string(),
        Reg::RDI => "rdi".to_string(),
        Reg::RSI => "rsi".to_string(),
        Reg::R10 => "r10".to_string(),
        Reg::RBP => "rbp".to_string(),
        Reg::R11 => "r11".to_string(),
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
                let sign_i = if *i < 0 { "-" } else { "+" };
                format!("[{}{}{}]", reg_to_str(r), sign_i, i.abs())
            }
        }
    }
}

fn compile_function_to_instrs(
    func: &Function,
    tag_id: &mut i32,
    instr_vec: &mut Vec<Instr>,
    defns: &ProgDefns,
) -> ExprType {
    // Set up the function prologue for our_code_starts_here
    instr_vec.push(Instr::IComment("Function prologue".to_string()));

    instr_vec.extend(FUNCTION_PROLOGUE);

    let scope = &mut VariableScope::new();
    let mut rbp_offset = 0;

    // Build the variable scope starting with arguments

    let mut existing_identifiers: HashSet<String> = HashSet::new();

    for (i, arg) in func.signature.arg_types.iter().enumerate() {
        if existing_identifiers.contains(&arg.0) {
            panic!("Duplicate param");
        }
        existing_identifiers.insert(arg.0.to_string());
        let arg_rbp_offset = i32::try_from(i + 2).unwrap() * SIZE_OF_NUMBER;
        scope.insert(arg.0.clone(), (arg_rbp_offset, arg.1.clone()));
    }

    // Add `input` as a local variable if the function being parsed is main
    if func.signature.name == MAIN_FN_TAG {
        instr_vec.push(Instr::IPush(Val::Reg(Reg::RDI)));
        rbp_offset -= SIZE_OF_NUMBER;

        scope.insert("input".to_string(), (rbp_offset, ExprType::Number));
    }

    // Compile the function body
    instr_vec.push(Instr::IComment("Function body".to_string()));

    let evaluated_return_type =
        compile_to_instrs(&func.body, scope, instr_vec, &mut rbp_offset, tag_id, defns);

    // Call print function with final result if this is the main function
    if func.signature.name == MAIN_FN_TAG {
        instr_vec.push(Instr::IComment("Print final result".to_string()));
        instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
        instr_vec.push(Instr::IMov(
            Val::Reg(Reg::RSI),
            Val::Imm(evaluated_return_type.to_type_flag()),
        ));

        // Ensure 16-byte stack alignment prior to calling snek_print

        // Move rsp to most recent stack-allocated local variable
        instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
        instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(rbp_offset)));
        instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

        instr_vec.push(ALIGN_RSP_16_BYTES);
        instr_vec.push(Instr::ICall("snek_print".to_string()));

        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::RBX)));
    };
    instr_vec.push(Instr::IComment("Function epilogue".to_string()));
    instr_vec.extend(FUNCTION_EPILOGUE);

    func.signature.return_type.clone()
}

pub fn compile(p: &Prog, defns: &ProgDefns) -> String {
    // Compile all functions to instruction strings
    let mut tag_id: i32 = 0;
    let mut asm_string: String = "extern snek_print
extern snek_error
extern malloc

section .text
global our_code_starts_here

overflow_error:
  mov rdi, 3
  and rsp, -16
  call snek_error
"
    .to_string();

    for func in p {
        let mut instr_vec: Vec<Instr> = Vec::new();
        let _func_return_type =
            compile_function_to_instrs(func, &mut tag_id, &mut instr_vec, defns);

        let asm_func_string = format!(
            "
{}:
{}
",
            func.signature.name,
            compile_instrs_to_str(&instr_vec)
        );

        asm_string.push_str(&asm_func_string);
    }

    asm_string
}
