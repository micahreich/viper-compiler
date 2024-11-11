use core::panic;
use std::collections::HashSet;

use crate::types::*;

fn push_reg_to_stack(instr_vec: &mut Vec<Instr>, rbp_offset: i32, reg: Reg) -> i32 {
    let new_rbp_offset = rbp_offset - SIZE_OF_DWORD;

    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RBP, new_rbp_offset),
        Val::Reg(reg),
    ));

    new_rbp_offset
}

fn round_up_to_next_multiple_of_16(n: i32) -> i32 {
    (n + 15) & !15
}

fn stack_space_needed(e: &Expr) -> i32 {
    match e {
        Expr::Boolean(_) | Expr::Number(_) | Expr::Id(_) => 0,
        Expr::UnOp(op1, e) => {
            match op1 {
                Op1::Print => {
                    // For print we need to push (1 value) RAX to the stack to save it before calling `snek_print`
                    SIZE_OF_DWORD + stack_space_needed(e)
                },
                _ => stack_space_needed(e),
            }
        }
        Expr::BinOp(_, e1, e2) => {
            // For binary operations, we need to push the result of e2 to the stack
            SIZE_OF_DWORD + stack_space_needed(e1) + stack_space_needed(e2)
        },
        Expr::Let(bindings, e) => {
            // We push the evaluation of each binding to the stack
            let mut space_needed = i32::try_from(bindings.len()).unwrap() * SIZE_OF_DWORD;

            for (_, binding_e) in bindings {
                space_needed += stack_space_needed(binding_e);
            }

            space_needed + stack_space_needed(e) // Also considering stack space needed for let body expression
        }
        Expr::Set(_, e) => stack_space_needed(e),
        Expr::Block(expr_vec) => {
            let mut space_needed = 0;
            for e in expr_vec {
                space_needed += stack_space_needed(e);
            }
            space_needed
        }
        Expr::If(e1, e2, e3) => {
            // We only end up needing stack space for evaluation or the TRUE or the
            // FALSE branch, not both
            stack_space_needed(e1) + std::cmp::max(
                stack_space_needed(e2),
                stack_space_needed(e3)
            )
        },
        Expr::RepeatUntil(e1, e2) => {
            // We need stack space for the evaluation of e1, then 1 extra dword for 
            // storing the result of that evaluation; also need space for body of loop
            SIZE_OF_DWORD + stack_space_needed(e1) + stack_space_needed(e2)
        }
        Expr::Call(_, args) => {
            // We push all arguments to the function call onto the stack
            let mut space_needed = i32::try_from(args.len()).unwrap() * SIZE_OF_DWORD;

            for e in args {
                space_needed += stack_space_needed(e);
            }
            space_needed
        }
        // Expr::Lookup(e1, _) => stack_space_needed(e1, defns),
        // Expr::RecordInitializer(_, fields) => {
        //     let mut space_needed = 0;
        //     for e in fields {
        //         space_needed += stack_space_needed(e, defns);
        //     }

        //     // We need to allocate 2 additional dwords, 1 for the refcount pointer and
        //     // 1 for the raw record pointer

        //     space_needed
        // }
    }
}

fn compile_to_instrs(
    e: &Expr,
    scope: &mut VariableScope,
    instr_vec: &mut Vec<Instr>,
    rbp_offset: &mut i32,
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
        Expr::Id(s) => match scope.get(s) {
            Some((s_rbp_offset, e_type)) => {
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, *s_rbp_offset),
                ));

                *e_type
            }
            None => panic!("Invalid: Unbound variable identifier {s}"),
        },
        Expr::UnOp(op, e) => {
            let e_type: ExprType = compile_to_instrs(e, scope, instr_vec, rbp_offset, tag_id);
            
            match op {
                Op1::Print => {
                    let e_rbp_offset = push_reg_to_stack(instr_vec, *rbp_offset, Reg::RAX);
                    *rbp_offset = e_rbp_offset;

                    instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RSI),
                        Val::Imm(e_type.to_type_flag()),
                    ));

                    // // Move rsp to most recent stack-allocated local variable
                    // instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
                    // instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(*rbp_offset)));
                    // instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

                    // // Align rsp to 16 bytes
                    // instr_vec.push(ALIGN_RSP_16_BYTES);

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

            e_type
        }
        Expr::BinOp(op, e1, e2) => {
            // Compile e2 first so that subtraction works nicely, leaves e1 in rax
            let e2_type = compile_to_instrs(e2, scope, instr_vec, rbp_offset, tag_id);
            let rbp_offset_e2_eval = push_reg_to_stack(instr_vec, *rbp_offset, Reg::RAX);
            *rbp_offset = rbp_offset_e2_eval;

            let e1_type = compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id); // e1 is in rax

            // Perform some type checking on the arguments
            if *op == Op2::Equal && e1_type != e2_type {
                panic!("Type mismatch in equality comparison");
            } else if (*op != Op2::Equal) && !(e1_type == ExprType::Number && e2_type == ExprType::Number) {
                panic!("Type mismatch for binary operation {:?}", op);
            }

            if matches!(
                op,
                Op2::Equal | Op2::Less | Op2::LessEqual | Op2::Greater | Op2::GreaterEqual
            ) {
                instr_vec.push(Instr::ICmp(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                ));
                instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));
                
                match op {
                    Op2::Equal => {
                        // instr_vec.push(Instr::ICmp(
                        //     Val::Reg(Reg::RAX),
                        //     Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        // ));

                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));
                        instr_vec.push(Instr::ICMovEqual(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::Less => {
                        // instr_vec.push(Instr::ICmp(
                        //     Val::Reg(Reg::RAX),
                        //     Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        // ));

                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));
                        instr_vec.push(Instr::ICMovLess(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::LessEqual => {
                        // instr_vec.push(Instr::ICmp(
                        //     Val::Reg(Reg::RAX),
                        //     Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        // ));

                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));
                        instr_vec.push(Instr::ICMovLessEqual(
                            Val::Reg(Reg::RAX),
                            Val::Reg(Reg::R10),
                        ));
                    }
                    Op2::Greater => {
                        // instr_vec.push(Instr::ICmp(
                        //     Val::Reg(Reg::RAX),
                        //     Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        // ));

                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));
                        instr_vec.push(Instr::ICMovGreater(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::GreaterEqual => {
                        // instr_vec.push(Instr::ICmp(
                        //     Val::Reg(Reg::RAX),
                        //     Val::RegOffset(Reg::RBP, rbp_offset_e2_eval),
                        // ));

                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));
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

                let var_e_type = compile_to_instrs(var_e, scope, instr_vec, rbp_offset, tag_id);
                *rbp_offset = push_reg_to_stack(instr_vec, *rbp_offset, Reg::RAX);

                if !existing_identifiers.insert(var.clone()) {
                    panic!("Duplicate binding in let expression");
                } 

                scope.insert(var.clone(), (*rbp_offset, var_e_type));
            }

            // Compile the expression
            let e_type = compile_to_instrs(e, scope, instr_vec, rbp_offset, tag_id);

            // Restore original scope after the let expression is finished
            *scope = original_scope;

            e_type
        }
        Expr::Set(id, e1) => {
            let e1_type = compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id);
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
                last_e_type = compile_to_instrs(e, scope, instr_vec, rbp_offset, tag_id);
            }

            last_e_type
        }
        Expr::If(e1, e2, e3) => {
            let curr_tag_id = *tag_id;
            *tag_id += 1;

            // Compile e1 (if condition)
            compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id);

            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));

            // If e1 evaluates to false, go to e3 (false branch)
            instr_vec.push(Instr::IJumpEqual(format!("else{curr_tag_id}")));

            // Compile e2 (true branch)
            let return_type_true_branch = compile_to_instrs(e2, scope, instr_vec, rbp_offset, tag_id);
            instr_vec.push(Instr::IJump(format!("end{curr_tag_id}")));

            // Compile e3 (false branch)
            instr_vec.push(Instr::ITag(format!("else{curr_tag_id}")));
            let return_type_false_branch = compile_to_instrs(e3, scope, instr_vec, rbp_offset, tag_id);
            
            if return_type_true_branch != return_type_false_branch {
                panic!("Type mismatch in if-else branches");
            }

            instr_vec.push(Instr::ITag(format!("end{curr_tag_id}")));

            return_type_true_branch
        }
        Expr::RepeatUntil(e1, e2) => {
            let curr_tag_id = *tag_id;
            *tag_id += 1;

            instr_vec.push(Instr::ITag(format!("loop{curr_tag_id}")));

            // Compile e1 (loop body)
            let return_type_loop_body = compile_to_instrs(e1, scope, instr_vec, rbp_offset, tag_id);
            let rbp_offset_loop_body_e = push_reg_to_stack(instr_vec, *rbp_offset, Reg::RAX);
            *rbp_offset = rbp_offset_loop_body_e;

            // Compile e2 (loop condition)
            compile_to_instrs(e2, scope, instr_vec, rbp_offset, tag_id);

            // If e2 returned false, jump back to top of loop
            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            instr_vec.push(Instr::IJumpEqual(format!("loop{curr_tag_id}")));

            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, rbp_offset_loop_body_e),
            ));

            instr_vec.push(Instr::ITag(format!("end{curr_tag_id}")));

            return_type_loop_body
        }
        Expr::Call(func_sig, args) => {
            // let prev_rbp_offset = *rbp_offset;

            // let n_args = i32::try_from(args.len()).unwrap();
            // let stack_space_to_align = round_up_to_next_multiple_of_16(n_args * SIZE_OF_DWORD);

            // Evaluate all the function arguments
            // let mut evaluated_args_rbp_offsets: Vec<i32> = Vec::new();

            for (i, arg_expr) in args.iter().enumerate(){
                let _arg_type = compile_to_instrs(arg_expr, scope, instr_vec, rbp_offset, tag_id);
                
                // Push the evaluated arguments onto the stack in the correct order, using the
                // following ordering convention:
                // [arg 4] 0x20
                // [arg 3] 0x18
                // [arg 2] 0x10
                // [arg 1] 0x08 <- $rsp

                instr_vec.push(Instr::IMov(
                    Val::RegOffset(Reg::RSP, i32::try_from(i).unwrap() * SIZE_OF_DWORD), Val::Reg(Reg::RAX))
                );
                
                // let rbp_offset_arg = push_reg_to_stack(instr_vec, *rbp_offset);
                // *rbp_offset = rbp_offset_arg;

                // evaluated_args_rbp_offsets.push(rbp_offset_arg);
            }

            // // Move rsp to most recent stack-allocated local variable
            // instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
            // instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(*rbp_offset)));
            // instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

            // // Align rsp to 16 bytes
            // instr_vec.push(ALIGN_RSP_16_BYTES);

            // // Reserve space on the stack for the arguments
            // instr_vec.push(Instr::ISub(
            //     Val::Reg(Reg::RSP),
            //     Val::Imm(stack_space_to_align),
            // ));

            // // Put the arguments onto the stack in the correct order
            // for (i, arg_rbp_offset) in evaluated_args_rbp_offsets.iter().enumerate() {
            //     let rsp_offset = i32::try_from(i).unwrap() * SIZE_OF_DWORD; // positive offset from $rsp

            //     // Move the argument from the stack to a temp register
            //     instr_vec.push(Instr::IMov(
            //         Val::Reg(Reg::R11),
            //         Val::RegOffset(Reg::RBP, *arg_rbp_offset),
            //     ));

            //     instr_vec.push(Instr::IMov(
            //         Val::RegOffset(Reg::RSP, rsp_offset),
            //         Val::Reg(Reg::R11),
            //     ));
            // }

            // Call the function
            instr_vec.push(Instr::ICall(func_sig.name.clone()));

            // // Restore the rbp_offset to before we allocated space for the arguments
            // *rbp_offset = prev_rbp_offset;

            func_sig.return_type
        }
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
        Instr::IEnter(n_bytes) => format!("enter {}, 0", n_bytes),
        Instr::ILeave => "leave".to_string(),
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
        Val::RegOffsetImm(r, i) => {
            if *i == 0 {
                reg_to_str(r)
            } else {
                let sign_i = if *i < 0 { "-" } else { "+" };
                format!("{}{}{}", reg_to_str(r), sign_i, i.abs())
            }
        }
    }
}

fn compile_function_to_instrs(
    func: &Function,
    tag_id: &mut i32,
    instr_vec: &mut Vec<Instr>,
) -> ExprType {
    // Set up the function prologue for our_code_starts_here
    let stack_space_needed_n_bytes = stack_space_needed(&func.body) +
        if func.signature.name == MAIN_FN_TAG {
            SIZE_OF_DWORD
        } else {
            0
        };
    
    instr_vec.push(Instr::IEnter(round_up_to_next_multiple_of_16(stack_space_needed_n_bytes)));

    let scope = &mut VariableScope::new();

    // Build the variable scope starting with arguments

    let mut existing_identifiers: HashSet<String> = HashSet::new();

    for (i, arg) in func.signature.arg_types.iter().enumerate() {
        if !existing_identifiers.insert(arg.0.to_string()) {
            panic!("Duplicate param");
        }

        let arg_rbp_offset = i32::try_from(i + 2).unwrap() * SIZE_OF_DWORD;
        scope.insert(arg.0.clone(), (arg_rbp_offset, arg.1));
    }

    let mut rbp_offset = 0;

    // Add `input` as a local variable if the function being parsed is main
    if func.signature.name == MAIN_FN_TAG {
        // instr_vec.push(Instr::IPush(Val::Reg(Reg::RDI)));
        // rbp_offset -= SIZE_OF_DWORD;
        rbp_offset = push_reg_to_stack(instr_vec, rbp_offset, Reg::RDI);
        scope.insert("input".to_string(), (rbp_offset, ExprType::Number));
    }

    // Compile the function body
    let evaluated_return_type = compile_to_instrs(&func.body, scope, instr_vec, &mut rbp_offset, tag_id);

    // Call print function with final result if this is the main function
    if func.signature.name == MAIN_FN_TAG {
        instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
        instr_vec.push(Instr::IMov(
            Val::Reg(Reg::RSI),
            Val::Imm(evaluated_return_type.to_type_flag()),
        ));

        // Ensure 16-byte stack alignment prior to calling snek_print

        // // Move rsp to most recent stack-allocated local variable
        // instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
        // instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(rbp_offset)));
        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

        // instr_vec.push(ALIGN_RSP_16_BYTES);
        instr_vec.push(Instr::ICall("snek_print".to_string()));

        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::RBX)));
    };

    instr_vec.extend(FUNCTION_EPILOGUE);

    func.signature.return_type
}

pub fn compile(p: &Prog) -> String {
    // Compile all functions to instruction strings
    let mut tag_id: i32 = 0;
    let mut asm_string: String = "
extern snek_print
extern snek_error

section .text
global our_code_starts_here

overflow_error:
  mov rdi, 3
  call snek_error
"
    .to_string();

    for func in p {
        let mut instr_vec: Vec<Instr> = Vec::new();
        let _func_return_type = compile_function_to_instrs(func, &mut tag_id, &mut instr_vec);

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
