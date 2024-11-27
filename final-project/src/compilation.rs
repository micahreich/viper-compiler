use core::panic;

use crate::types::*;

fn push_reg_to_stack(instr_vec: &mut Vec<Instr>, rbp_offset: i32, reg: Reg) -> i32 {
    let new_rbp_offset = rbp_offset - SIZE_OF_DWORD;

    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RBP, new_rbp_offset),
        Val::Reg(reg),
    ));

    new_rbp_offset
}

fn push_val_to_stack(instr_vec: &mut Vec<Instr>, rbp_offset: i32, val: i32) -> i32 {
    let new_rbp_offset = rbp_offset - SIZE_OF_DWORD;

    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RBP, new_rbp_offset),
        Val::Imm(val),
    ));

    new_rbp_offset
}

fn push_rbx_to_stack(instr_vec: &mut Vec<Instr>, rbx_offset: i32) -> i32 {
    let new_rbx_offset = rbx_offset - SIZE_OF_DWORD;

    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RBP, new_rbx_offset), 
        Val::Reg(Reg::RBX)
    ));

    new_rbx_offset
}

fn pop_rbx_from_stack(instr_vec: &mut Vec<Instr>, rbx_offset: i32) -> i32 {
    let new_rbx_offset = rbx_offset + SIZE_OF_DWORD;

    instr_vec.push(Instr::IMov(
        Val::Reg(Reg::RBX),
        Val::RegOffset(Reg::RBP, rbx_offset),
    ));

    new_rbx_offset
}

fn set_carry_forward(instr_vec: &mut Vec<Instr>, val: bool) {
    instr_vec.push(
        Instr::IMov(Val::Reg(Reg::RBX),
        Val::Imm(i32::from(val)))
    );
}

fn push_rbx_and_set_carry_forward(instr_vec: &mut Vec<Instr>, rbx_offset: i32, val: bool) -> i32 {
    let new_rbx_offset = push_rbx_to_stack(instr_vec, rbx_offset);
    set_carry_forward(instr_vec, val);

    new_rbx_offset
}


fn calculate_record_size(signature: &RecordSignature) -> i32 {
    return i32::try_from(
        (signature.field_types.len() + 1) * SIZE_OF_DWORD as usize,
    )
    .expect("Record size (+1) in bytes exceeds i32 max value");
}

fn round_up_to_next_multiple_of_16(n: i32) -> i32 {
    println!("Rounding up: {} to {}", n, (n + 15) & !15);
    (n + 15) & !15
}

fn stack_space_needed(e: &Expr) -> i32 {
    match e {
        Expr::Boolean(_) | Expr::Number(_) | Expr::Id(_) => 0,
        Expr::UnOp(op1, e) => {
            match op1 {
                Op1::Print => {
                    stack_space_needed(e) + // Evaluate the expression to be printed
                    2 * SIZE_OF_DWORD // Save RAX on the stack to restore after print call
                }
                _ => stack_space_needed(e),
            }
        }
        Expr::BinOp(_, e1, e2) => {
            // For binary operations, we need to push the result of e2 to the stack
            SIZE_OF_DWORD + stack_space_needed(e1) + stack_space_needed(e2)
        }
        Expr::Let(bindings, e) => {
            // We push the evaluation of each binding to the stack
            let mut space_needed = 0;

            for (_, binding_e) in bindings {
                space_needed += stack_space_needed(binding_e);
                space_needed += SIZE_OF_DWORD;
            }

            space_needed + // Space needed for bindings eval + storage
            stack_space_needed(e) + // Space needed for let body expression
            1 * SIZE_OF_DWORD // Space needed to temporarily store body eval
        }
        Expr::Set(_, e) => {
            stack_space_needed(e) + 1 * SIZE_OF_DWORD // Space needed to store evaluated RHS expression
        }
        Expr::Block(expr_vec) => {
            expr_vec
                .iter()
                .fold(0, |acc, e| acc + stack_space_needed(e))
        }
        Expr::If(e_cond, e_true, e_false) => {
            // We only end up needing stack space for evaluation or the TRUE or the
            // FALSE branch, not both
            stack_space_needed(e_cond)
            + std::cmp::max(stack_space_needed(e_true), stack_space_needed(e_false))
        }
        Expr::RepeatUntil(e1, e2) => {
            // We need stack space for the evaluation of e1, e2, and 1 extra dword for
            // storing body evaluation result
            stack_space_needed(e1) + stack_space_needed(e2) + 1 * SIZE_OF_DWORD
        }
        Expr::Call(_, args) => {
            // We push all arguments to the function call onto the stack
            args
                .iter()
                .fold(0, |acc, e| acc + (stack_space_needed(e) + 2 * SIZE_OF_DWORD))
        }
        Expr::Lookup(e1, _) => stack_space_needed(e1) + 2 * SIZE_OF_DWORD,
        Expr::RecordInitializer(_, fields) => {
            fields
                .iter()
                .fold(SIZE_OF_DWORD, |acc, e| acc + stack_space_needed(e))
            
            // let mut space_needed = 1 * SIZE_OF_DWORD;

            // for e in fields {
            //     space_needed += stack_space_needed(e);
            // }

            // // We need to allocate 2 additional dwords, 1 for the refcount pointer and
            // // 1 for the raw record pointer

            // space_needed
        }
        Expr::RecordSetField(_, _, expr) => {
            stack_space_needed(expr) + 1 * SIZE_OF_DWORD
        }
    }
}

fn rbx_storage_stack_space_needed(e: &Expr) -> i32 {
    match e {
        Expr::Number(_)
        | Expr::Boolean(_)
        | Expr::Id(_) 
        | Expr::UnOp(_, _)
        | Expr::BinOp(_, _, _) => 0,
        Expr::Let(bindings, expr) => {
            // We push the evaluation of each binding to the stack
            let space_needed_for_e = bindings
                .iter()
                .fold(0, |acc, (_, binding_expr)| std::cmp::max(acc, rbx_storage_stack_space_needed(binding_expr)));
            
            std::cmp::max(
                rbx_storage_stack_space_needed(expr),
                space_needed_for_e + SIZE_OF_DWORD
            )
        },
        Expr::If(expr_cond, expr_true, expr_false) => {
            let space_needed_for_branches = std::cmp::max(
                rbx_storage_stack_space_needed(expr_true),
                rbx_storage_stack_space_needed(expr_false)
            );

            std::cmp::max(
                SIZE_OF_DWORD + rbx_storage_stack_space_needed(expr_cond),
                space_needed_for_branches
            )
        }
        Expr::RepeatUntil(expr_guard, expr_loop_body) => {
            std::cmp::max(
                rbx_storage_stack_space_needed(expr_loop_body),
                SIZE_OF_DWORD + rbx_storage_stack_space_needed(expr_guard)
            )
        }
        Expr::Set(_, expr) => {
            SIZE_OF_DWORD + rbx_storage_stack_space_needed(expr)
        }
        Expr::RecordSetField(_, _, expr) => {
            SIZE_OF_DWORD + rbx_storage_stack_space_needed(expr)
        }
        Expr::Block(expr_vec) => {
            let space_needed_for_block = expr_vec
                .iter()
                .fold(0, |acc, e| std::cmp::max(acc, rbx_storage_stack_space_needed(e)));            
            
            space_needed_for_block + SIZE_OF_DWORD
        },
        // TODO @mreich: technically carry forward will always be set to true in this AST block,
        // but should probably explicitly set it to 1 for clarity
        Expr::RecordInitializer(_, _) => 0,
        Expr::Call(_, args_vec) => {
            let space_needed_for_args = args_vec
                .iter()
                .fold(0, |acc, e| std::cmp::max(acc, rbx_storage_stack_space_needed(e)));            
            
            space_needed_for_args + SIZE_OF_DWORD
        }
        Expr::Lookup(expr, _) => {
            rbx_storage_stack_space_needed(expr) + SIZE_OF_DWORD
        }
    }
}

fn compile_to_instrs(
    e: &Expr,
    ctx: &mut CompileCtx,
    instr_vec: &mut Vec<Instr>,
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
        Expr::Id(s) => match ctx.scope.get(s) {
            Some((s_rbp_offset, e_type)) => {
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, *s_rbp_offset),
                ));

                // Check carry forward assignment for refcnt pointers, increment refcnt by 1
                if let ExprType::RecordPointer(_) = e_type {
                    instr_vec.extend(vec![
                        Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)),
                        Instr::ICall("rc_incr".to_string()),
                    ]);
                }

                // if ctx.carry_fwd_assignment && matches!(e_type, ExprType::RecordPointer(_)) {
                //     instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
                //     ctx.tag_id += 1;
                //     let null_end_tag = format!("null_check{}", ctx.tag_id);
                //     instr_vec.push(Instr::IJumpEqual(null_end_tag.clone()));
                //     instr_vec.push(Instr::IAdd(Val::RegOffset(Reg::RAX, 0), Val::Imm(1)));
                //     instr_vec.push(Instr::ITag(null_end_tag));
                // }

                e_type.clone()
            }
            None => {
                if s == "NULL" {
                    instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                    ExprType::RecordNullPtr
                } else {
                    panic!("Invalid: Unbound variable identifier {s}");
                }
            }
        },
        Expr::UnOp(op, e) => {
            // instr_vec.push(Instr::IComment("Save RBX before field lookup".to_string()));

            // let rbx_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
            // ctx.rbp_offset = rbx_offset;

            // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(1)));

            // let e_type: ExprType = compile_to_instrs(e, ctx, instr_vec, defns);

            // // Restore RBX
            // instr_vec.extend(vec![
            //     Instr::IComment("Restore RBX after field lookup".to_string()),
            //     Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, rbx_offset)),
            // ]);

            let e_type: ExprType = compile_to_instrs(e, ctx, instr_vec, defns);

            match op {
                Op1::Print => {
                    if let ExprType::RecordPointer(name) = &e_type {
                        
                        // todo!();
                        let e_rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                        ctx.rbp_offset = e_rbp_offset;

                        let record_def = defns.record_signatures.get(name).expect("Record definition not found");
                        // // Let's first print the contents
                        // // if one of the contents is a pointer to another, we need to recursively call compile

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Reg(Reg::RAX)));

                        // // print open parens
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RDI),
                            Val::Imm(0),
                        ));
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RSI),
                            Val::Imm(5),
                        ));

                        instr_vec.push(Instr::ICall("snek_print".to_string()));

                        for (i, field_expr) in record_def.field_types.iter().enumerate() {
                            instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::R10, i32::try_from(i+1).unwrap() * SIZE_OF_DWORD)));
                            instr_vec.push(Instr::IMov(
                                Val::Reg(Reg::RSI),
                                Val::Imm(field_expr.1.to_type_flag()),
                            ));

                            instr_vec.push(Instr::ICall("snek_print".to_string()));
                        }

                        // // print closed parens
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RDI),
                            Val::Imm(1),
                        ));
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RSI),
                            Val::Imm(5),
                        ));


                        instr_vec.push(Instr::ICall("snek_print".to_string()));

                        // // Print statements should evaluate to the given value
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RBP, e_rbp_offset),
                        ));
                    } else {
                        let e_rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                        ctx.rbp_offset = e_rbp_offset;

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RSI),
                            Val::Imm(e_type.to_type_flag()),
                        ));

                        instr_vec.push(Instr::ICall("snek_print".to_string()));

                        // Print statements should evaluate to the given printed value
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RBP, e_rbp_offset),
                        ));
                    }
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
            let e2_type = compile_to_instrs(e2, ctx, instr_vec, defns);
            let rbp_offset_e2_eval = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
            ctx.rbp_offset = rbp_offset_e2_eval;

            let e1_type = compile_to_instrs(e1, ctx, instr_vec, defns); // e1 is in rax

            // let is_comparing_record_to_null = (*op == Op2::Equal) &&
            //     (matches!(e1_type, ExprType::RecordPointer(_)) && e2_type == ExprType::RecordNullPtr ||
            //     e1_type == ExprType::RecordNullPtr && matches!(e2_type, ExprType::RecordPointer(_)));

            match op {
                Op2::Equal => match (e1_type, e2_type) {
                    (ExprType::RecordPointer(name1), ExprType::RecordPointer(name2)) => {
                        if name1 != name2 {
                            panic!(
                                "Type mismatch in equality comparison: cannot compare records of type {name1:?} and {name2:?}",
                            );
                        }
                    }
                    (ExprType::RecordPointer(_), ExprType::RecordNullPtr) => {}
                    (ExprType::RecordNullPtr, ExprType::RecordPointer(_)) => {}
                    (t1, t2) => {
                        if t1 != t2 {
                            panic!(
                                "Type mismatch in equality comparison: cannot compare expressions of type {t1:?} and {t2:?}",
                            );
                        }
                    }
                },
                _ => {
                    if e1_type != ExprType::Number || e2_type != ExprType::Number {
                        panic!("Invalid type for binary operation");
                    }
                }
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
                        instr_vec.push(Instr::ICMovEqual(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::Less => {
                        instr_vec.push(Instr::ICMovLess(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::LessEqual => {
                        instr_vec.push(Instr::ICMovLessEqual(
                            Val::Reg(Reg::RAX),
                            Val::Reg(Reg::R10),
                        ));
                    }
                    Op2::Greater => {
                        instr_vec.push(Instr::ICMovGreater(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::GreaterEqual => {
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
            let original_scope = ctx.scope.clone();

            // Add the bindings from the scope
            let mut newly_created_variable_scope: VariableScope = VariableScope::new();

            // let old_ctx_carry_fwd_assignment = ctx.carry_fwd_assignment;
            // ctx.carry_fwd_assignment = true;

            // Track the old carry forward assignment value, temporarily set to 1 for let bindings
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, true);
            
            // instr_vec.push(Instr::IComment("Save RBX before let bindings".to_string()));

            // let rbx_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
            // ctx.rbp_offset = rbx_offset;

            // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(1)));
            // set_carry_forward(instr_vec, true);

            for (var_name, var_e) in bindings {
                if !is_valid_identifier(var_name) && var_name != "input" {
                    panic!("Reserved keyword or invalid identifier used as variable name in let expression: {var_name}");
                }

                let var_e_type = compile_to_instrs(var_e, ctx, instr_vec, defns);
                ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);

                if newly_created_variable_scope
                    .insert(var_name.clone(), (ctx.rbp_offset, var_e_type.clone()))
                    .is_some()
                {
                    panic!("Duplicate binding in let expression");
                }

                ctx.scope
                    .insert(var_name.clone(), (ctx.rbp_offset, var_e_type.clone()));
            }
            // ctx.carry_fwd_assignment = old_ctx_carry_fwd_assignment;

            // Restore RBX
            // instr_vec.extend(vec![
            //     Instr::IComment("Restore RBX after let bindings".to_string()),
            //     Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, rbx_offset)),
            // ]);
            ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

            // Compile the expression
            let e_type = compile_to_instrs(e, ctx, instr_vec, defns);
            ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);

            // Check for any pointer types in the bindings and decrement the references
            for (_var_name, (offset, e_type)) in newly_created_variable_scope.iter() {
                if let ExprType::RecordPointer(record_name) = e_type {
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RDI),
                        Val::RegOffset(Reg::RBP, *offset),
                    ));
                    instr_vec.push(Instr::ICall(format!("{}_record_rc_decr", record_name)));
                }
            }

            // Move the final result of the expression evaluatoin into RAX
            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, ctx.rbp_offset),
            ));

            // Restore original scope after the let expression is finished
            ctx.scope = original_scope;

            e_type
        }
        Expr::Set(id, e1) => {
            // We're setting id = eval(e1), so we are assigning the evaluation result to id meaning
            // we need to carry forward the assignment flag

            // let old_ctx_carry_fwd_assignment = ctx.carry_fwd_assignment;
            // ctx.carry_fwd_assignment = true;

            let (id_offset, id_type) = ctx
                .scope
                .get(id)
                .expect("Variable not found in scope during set expression")
                .clone();

            if let ExprType::RecordPointer(record_name) = id_type.clone() {
                // Track the old carry forward assignment value, temporarily set to 1 for set bindings
                // instr_vec.push(Instr::IComment(
                //     "Save RBX before set! expression".to_string(),
                // ));

                // let rbx_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
                // ctx.rbp_offset = rbx_offset;
                // ctx.rbx_offset = push_rbx_to_stack(instr_vec, ctx.rbx_offset);
                // set_carry_forward(instr_vec, true);

                ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, true);

                // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(1)));

                let e1_type = compile_to_instrs(e1, ctx, instr_vec, defns);

                ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

                if e1_type != id_type {
                    panic!(
                        "Type mismatch in set! expression, expected {id_type:?} but got {e1_type:?}"
                    );
                }

                // // Restore RBX
                // instr_vec.extend(vec![
                //     Instr::IComment("Restore RBX after set! expression".to_string()),
                //     Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, rbx_offset)),
                // ]);

                let e1_eval_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                ctx.rbp_offset = e1_eval_offset;

                // Decrement the refcount of what `id` was originally pointing to
                instr_vec.extend(vec![
                    Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::RBP, id_offset)),
                    Instr::ICall(format!("{}_record_rc_decr", record_name)),
                ]);

                // Move the evaluated value of e1 into the place on the stack where `id` is stored
                instr_vec.extend(vec![
                    Instr::IComment(format!("Move evaluated value of e1 into place of {}", id)),
                    Instr::IMov(Val::Reg(Reg::R11), Val::RegOffset(Reg::RBP, e1_eval_offset)),
                    Instr::IMov(Val::RegOffset(Reg::RBP, id_offset), Val::Reg(Reg::R11)),
                    Instr::IMov(Val::Reg(Reg::RAX), Val::Reg(Reg::R11)),
                ]);
            } else {
                // TODO @dkrajews, @mreich: do we need to set RDI = 0 explicitly here?
                let e1_type = compile_to_instrs(e1, ctx, instr_vec, defns);

                if e1_type != id_type {
                    panic!(
                        "Type mismatch in set! expression, expected {id_type:?}, got {e1_type:?}"
                    );
                }

                instr_vec.extend(vec![
                    Instr::IComment(format!("Move evaluated value of e1 into place of {}", id)),
                    Instr::IMov(Val::RegOffset(Reg::RBP, id_offset), Val::Reg(Reg::RAX))
                ])
            }

            id_type.clone()
        }
        Expr::Block(expr_vec) => {
            // let old_ctx_carry_fwd_assignment = ctx.carry_fwd_assignment;
            // ctx.carry_fwd_assignment = false;

            // Track the old carry forward assignment value, temporarily set to 1 for set bindings
            // instr_vec.push(Instr::IComment(
            //     "Save RBX before block expression".to_string(),
            // ));

            // let rbx_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
            // ctx.rbp_offset = rbx_offset;

            // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(0)));
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, false);

            for (i, e) in expr_vec.iter().enumerate() {
                // Since the block evalualtes to the last expression, we need to carry forward the assignment
                // if we're at the last expression in the block; otherwise we say it's false

                if i == expr_vec.len() - 1 {
                    // Restore RBX
                    // instr_vec.extend(vec![
                    //     Instr::IComment(
                    //         "Restore RBX for last item in block expression".to_string(),
                    //     ),
                    //     Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, rbx_offset)),
                    // ]);
                    ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);
                    return compile_to_instrs(e, ctx, instr_vec, defns);
                }

                compile_to_instrs(e, ctx, instr_vec, defns);
            }

            panic!("Invalid: Empty block expression encountered");
        }
        Expr::If(e_condition, e_true, e_false) => {
            let curr_tag_id = ctx.tag_id;
            ctx.tag_id += 1;

            // Compile e1 (if condition)
            // Track the old carry forward assignment value, temporarily set to 0 for if condition
            // instr_vec.push(Instr::IComment("Save RBX before if condition".to_string()));

            // let rbx_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
            // ctx.rbp_offset = rbx_offset;

            // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(0)));
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, false);

            compile_to_instrs(e_condition, ctx, instr_vec, defns);

            // // Restore RBX
            // instr_vec.extend(vec![
            //     Instr::IComment("Restore RBX after if condition".to_string()),
            //     Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, rbx_offset)),
            // ]);
            ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);
            
            let rbp_starting_offset_from_condition = ctx.rbp_offset;
            let rbx_starting_offset_from_condition = ctx.rbx_offset;

            // If e1 evaluates to false, go to e3 (false branch)
            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            instr_vec.push(Instr::IJumpEqual(format!("else{curr_tag_id}")));

            // Compile e2 (true branch)
            let return_type_true_branch = compile_to_instrs(e_true, ctx, instr_vec, defns);
            instr_vec.push(Instr::IJump(format!("end{curr_tag_id}")));

            // Compile e3 (false branch)
            ctx.rbp_offset = rbp_starting_offset_from_condition;
            ctx.rbx_offset = rbx_starting_offset_from_condition;

            instr_vec.push(Instr::ITag(format!("else{curr_tag_id}")));
            let return_type_false_branch = compile_to_instrs(e_false, ctx, instr_vec, defns);

            if return_type_true_branch != return_type_false_branch {
                panic!("Type mismatch in if-else branches, got {return_type_true_branch:?} and {return_type_false_branch:?}");
            }

            instr_vec.push(Instr::ITag(format!("end{curr_tag_id}")));

            return_type_true_branch
        }
        Expr::RepeatUntil(e1, e2) => {
            let curr_tag_id = ctx.tag_id;
            ctx.tag_id += 1;

            instr_vec.push(Instr::ITag(format!("loop{curr_tag_id}")));

            // Compile e1 (loop body)
            let return_type_loop_body = compile_to_instrs(e1, ctx, instr_vec, defns);
            let rbp_offset_loop_body_e = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
            ctx.rbp_offset = rbp_offset_loop_body_e;

            // Compile e2 (loop condition)

            // Track the old carry forward assignment value, temporarily set to 0 for loop guard
            // instr_vec.push(Instr::IComment("Save RBX before loop guard".to_string()));

            // let rbx_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
            // ctx.rbp_offset = rbx_offset;

            // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(0)));
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, false);

            compile_to_instrs(e2, ctx, instr_vec, defns);

            // // Restore RBX
            // instr_vec.extend(vec![
            //     Instr::IComment("Restore RBX after loop guard".to_string()),
            //     Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, rbx_offset)),
            // ]);
            ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

            // If e2 returned false, jump back to top of loop
            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            instr_vec.push(Instr::IJumpEqual(format!("loop{curr_tag_id}")));

            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, rbp_offset_loop_body_e),
            ));

            return_type_loop_body
        }
        Expr::Call(func_sig, args) => {
            // let old_carry_fwd = ctx.carry_fwd_assignment;
            // ctx.carry_fwd_assignment = true;

            // // Track the old carry forward assignment value, temporarily set to 1 for arguments
            // instr_vec.push(Instr::IComment(
            //     "Save RBX before fn argument evaluations".to_string(),
            // ));

            // let rbx_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
            // ctx.rbp_offset = rbx_offset;

            // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(1)));
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, true);

            let mut arg_evaluation_offsets: Vec<i32> = Vec::new();

            for arg_expr in args {
                let _arg_type = compile_to_instrs(arg_expr, ctx, instr_vec, defns);

                // Push the evaluated arguments onto the stack in the correct order, using the
                // following ordering convention:
                // [arg 4] 0x20
                // [arg 3] 0x18
                // [arg 2] 0x10
                // [arg 1] 0x08 <- $rsp

                let arg_i_rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                ctx.rbp_offset = arg_i_rbp_offset;

                arg_evaluation_offsets.push(arg_i_rbp_offset);
            }

            // ctx.carry_fwd_assignment = old_carry_fwd;

            // // Restore RBX
            // instr_vec.extend(vec![
            //     Instr::IComment("Restore RBX after fn argument evaluations".to_string()),
            //     Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, rbx_offset)),
            // ]);
            ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

            for (i, offset) in arg_evaluation_offsets.iter().enumerate() {
                instr_vec.extend(vec![
                    // Cut off david's balls and put them in a jar and then put them in a jar and also put them in a jar
                    Instr::IMov(Val::Reg(Reg::R11), Val::RegOffset(Reg::RBP, *offset)),
                    Instr::IMov(
                        Val::RegOffset(Reg::RSP, i32::try_from(i).unwrap() * SIZE_OF_DWORD),
                        Val::Reg(Reg::R11),
                    )
                ]);
            }

            // Call the function
            instr_vec.push(Instr::ICall(func_sig.name.clone()));

            // // Increment ref count of the return value if it's a record pointer
            // if let ExprType::RecordPointer(_) = func_sig.return_type {
            //     instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
            //     instr_vec.push(Instr::ICall("rc_incr".to_string()));
            // }

            // if ctx.carry_fwd_assignment && matches!(func_sig.return_type, ExprType::RecordPointer(_)) {
            //     // Increment the reference count of the field
            //     instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            //     ctx.tag_id += 1;
            //     let null_end_tag = format!("null_check{}", ctx.tag_id);
            //     instr_vec.push(Instr::IJumpEqual(null_end_tag.clone()));
            //     instr_vec.push(Instr::IAdd(Val::RegOffset(Reg::RAX, 0), Val::Imm(1)));
            //     instr_vec.push(Instr::ITag(null_end_tag));
            // }

            func_sig.return_type.clone()
        }
        Expr::Lookup(e1, field) => {
            // let old_carry_fwd = ctx.carry_fwd_assignment;
            // ctx.carry_fwd_assignment = false;

            // Track the old carry forward assignment value, temporarily set to 1 for field lookup
            // It's as though we temporarily create an alias to the record pointer for lookup, then we'll
            // decrement the refcount at the end of the lookup
            // instr_vec.push(Instr::IComment("Save RBX before field lookup".to_string()));

            // let rbx_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
            // ctx.rbp_offset = rbx_offset;

            // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(1)));
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, true);

            let e1_type = compile_to_instrs(e1, ctx, instr_vec, defns);

            // Restore RBX
            // instr_vec.extend(vec![
            //     Instr::IComment("Restore RBX after field lookup".to_string()),
            //     Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, rbx_offset)),
            // ]);
            ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

            let e1_addr_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
            ctx.rbp_offset = e1_addr_offset;

            if let ExprType::RecordPointer(record_name) = e1_type {
                let record_signature = defns.record_signatures.get(&record_name).unwrap();

                let field_index = record_signature
                    .field_types
                    .iter()
                    .position(|(field_name, _)| field_name == field);

                if let Some(idx) = field_index {
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RAX),
                        Val::RegOffset(Reg::RAX, i32::try_from(idx + 1).unwrap() * SIZE_OF_DWORD),
                    ));

                    let field_eval_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                    ctx.rbp_offset = field_eval_offset;

                    let return_type = record_signature.field_types[idx].1.clone();

                    // Increment the ref count for the field if it's a record pointer
                    if let ExprType::RecordPointer(_) = return_type {
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RDI),
                            Val::RegOffset(Reg::RBP, field_eval_offset),
                        ));
                        instr_vec.push(Instr::ICall("rc_incr".to_string()));
                    }

                    // if ctx.carry_fwd_assignment && matches!(return_type, ExprType::RecordPointer(_)) {
                    //     // Increment the reference count of the field
                    //     instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
                    //     ctx.tag_id += 1;
                    //     let null_end_tag = format!("null_check{}", ctx.tag_id);
                    //     instr_vec.push(Instr::IJumpEqual(null_end_tag.clone()));
                    //     instr_vec.push(Instr::IAdd(Val::RegOffset(Reg::RAX, 0), Val::Imm(1)));
                    //     instr_vec.push(Instr::ITag(null_end_tag));
                    // }

                    // Decrement the ref count of the record pointer which we're looking up with
                    // after the temporary increment from earlier
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RDI),
                        Val::RegOffset(Reg::RBP, e1_addr_offset),
                    ));
                    instr_vec.push(Instr::ICall(format!("{}_record_rc_decr", record_name)));

                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RAX),
                        Val::RegOffset(Reg::RBP, field_eval_offset),
                    ));

                    return_type
                } else {
                    panic!(
                        "Invalid field lookup: field {} not found in record {}",
                        field, record_name
                    );
                }
            } else {
                panic!("Invalid lookup expression, must be a non-null record pointer");
            }
        }
        Expr::RecordInitializer(record_name, fields) => {
            // If this isn't going to be assigned to a variable, we can just ignore the result
            instr_vec.push(Instr::IComment(format!(
                "Begin record initialization for record type {}",
                record_name
            )));

            ctx.tag_id += 1;
            let record_initialize_end_tag = format!("record_initialize_end{}", ctx.tag_id);

            instr_vec.extend(vec![
                Instr::ICmp(Val::Reg(Reg::RBX), Val::Imm(0)),
                Instr::IJumpEqual(record_initialize_end_tag.clone()),
            ]);

            // Call malloc
            if let Some(record_signature) = defns.record_signatures.get(record_name) {
                // Now allocate space for the record itself
                let n_bytes = calculate_record_size(record_signature);

                ctx.tag_id += 1;
                let heap_check_end_tag = format!("heap_check_end{}", ctx.tag_id);

                // let rbp_offset_record_ptr_eval =
                //     push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                // ctx.rbp_offset = rbp_offset_record_ptr_eval;

                // Check if out of memory
                instr_vec.extend(vec![
                    Instr::IAdd(Val::RegOffset(Reg::R12, CURRENT_HEAP_SIZE_R12_OFFSET), Val::Imm(n_bytes)),
                    Instr::IMov(Val::Reg(Reg::R11), Val::RegOffset(Reg::R12, CURRENT_HEAP_SIZE_R12_OFFSET)),
                    Instr::ICmp(Val::Reg(Reg::R11), Val::RegOffset(Reg::R12, MAX_HEAP_SIZE_R12_OFFSET)),
                    Instr::IJumpLess(heap_check_end_tag.to_string()),
                    Instr::ICall("out_of_memory_error".to_string()),
                    Instr::ITag(heap_check_end_tag)
                ]);

                instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(n_bytes)));

                instr_vec.push(Instr::ICall("malloc".to_string()));
                instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
                instr_vec.push(Instr::IJumpEqual("out_of_memory_error".to_string()));

                // Move rax into temporary stack place
                let rbp_offset_record_ptr_eval =
                    push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                ctx.rbp_offset = rbp_offset_record_ptr_eval;

                // Put a 1 in the reference count field
                instr_vec.push(Instr::IMov(Val::RegOffset(Reg::RAX, 0), Val::Imm(1)));

                // Initialize the rest of the fields
                instr_vec.push(Instr::IComment(format!(
                    "Fill in record fields for record type {record_name}",
                )));

                for (i, field_expr) in fields.iter().enumerate() {
                    let field_type_eval = compile_to_instrs(field_expr, ctx, instr_vec, defns);

                    if field_type_eval != ExprType::RecordNullPtr && field_type_eval != record_signature.field_types[i].1
                    {
                        panic!(
                            "Type mismatch in record initializer: ensure field type matches expression type, expected {:?} but got {:?}",
                            record_signature.field_types[i].1, field_type_eval
                        );
                    }
                    
                    instr_vec.extend(vec![
                        Instr::IMov(
                            Val::Reg(Reg::R11),
                            Val::RegOffset(Reg::RBP, rbp_offset_record_ptr_eval)
                        ),
                        Instr::IMov(
                            Val::RegOffset(Reg::R11, i32::try_from(i + 1).unwrap() * SIZE_OF_DWORD),
                            Val::Reg(Reg::RAX)
                        ),
                    ]);

                    // instr_vec.push(Instr::IMov(
                    //     Val::Reg(Reg::R11),
                    //     Val::RegOffset(Reg::RBP, rbp_offset_record_ptr_eval),
                    // ));

                    // instr_vec.push(Instr::IMov(
                    //     Val::RegOffset(Reg::R11, i32::try_from(i + 1).unwrap() * SIZE_OF_DWORD),
                    //     Val::Reg(Reg::RAX),
                    // ));
                }

                // Move the refcount pointer back into rax
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, rbp_offset_record_ptr_eval),
                ));

                instr_vec.push(Instr::ITag(record_initialize_end_tag));

                ExprType::RecordPointer(record_signature.name.clone())
            } else {
                panic!("Invalid record initializer: record {record_name} not found in definitions");
            }
        }
        Expr::RecordSetField(id, field_name, field_expr) => {
            let (id_offset, id_type) = ctx
                .scope
                .get(id)
                .expect("Variable not found in scope during set expression")
                .clone();
            
            if let ExprType::RecordPointer(record_type) = id_type {
                let record_signature = defns.record_signatures.get(&record_type).unwrap();
                
                let field_index = record_signature
                    .field_types
                    .iter()
                    .position(|(sig_field_name, _)| sig_field_name == field_name);

                if let Some(idx) = field_index {
                    // // Evalulate the new field expression
                    // instr_vec.push(Instr::IComment("Save RBX before new field expr evaluation".to_string()));

                    // let rbx_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
                    // ctx.rbp_offset = rbx_offset;

                    // instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(1)));
                    ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, true);
                    let return_type_field_expr = compile_to_instrs(field_expr, ctx, instr_vec, defns);
                    ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);
                    
                    let rbp_offset_field_expr_eval = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                    ctx.rbp_offset = rbp_offset_field_expr_eval;

                    // // Restore RBX
                    // instr_vec.extend(vec![
                    //     Instr::IComment("Restore RBX after field set expr evaluation".to_string()),
                    //     Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, rbx_offset)),
                    // ]);

                    let expected_return_type_field_expr = record_signature.field_types[idx].1.clone();
                    if return_type_field_expr != expected_return_type_field_expr {
                        panic!("Invalid: set! on record for field {field_name} does not match record signature,
                                expected: {expected_return_type_field_expr:?} but got: {return_type_field_expr:?}");
                    }

                    // Check if we're re-assigning to a RecordPointer field; if so, we must decrement the
                    // refcount of the old field. We also need to check the carry forward flag to see if this set!
                    // expression is being assigned to another variable

                    if let ExprType::RecordPointer(field_record_type) = expected_return_type_field_expr {
                        // Call rc_incr if we're doing something like x = set! record_name field my_record(...) since
                        // this set! expression DOES return the new field's value 
                        instr_vec.extend(vec![
                            Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::RBP, rbp_offset_field_expr_eval)),
                            Instr::ICall("rc_incr".to_string()),
                        ]);

                        // Decrement the reference count of the old value which was in this field
                        instr_vec.extend(vec![
                            Instr::IMov(Val::Reg(Reg::R11), Val::RegOffset(Reg::RBP, id_offset)),
                            Instr::IMov(
                                Val::Reg(Reg::RDI),
                                Val::RegOffset(Reg::R11, i32::try_from(idx + 1).unwrap() * SIZE_OF_DWORD),
                            ),
                            Instr::ICall(format!("{}_record_rc_decr", field_record_type)),
                        ]);
                    }

                    // Put the new field value in place in memory
                    instr_vec.extend(vec![
                        Instr::IMov(Val::Reg(Reg::R11), Val::RegOffset(Reg::RBP, id_offset)),
                        Instr::IMov(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RBP, rbp_offset_field_expr_eval),
                        ),
                        // Load the evaluated new field expression into memory at the field's location
                        Instr::IMov(
                            Val::RegOffset(Reg::R11, i32::try_from(idx + 1).unwrap() * SIZE_OF_DWORD),
                            Val::Reg(Reg::RAX),
                        ),
                    ]);

                    return_type_field_expr
                } else {
                    panic!("Invalid: set! on record for field {field_name} not found in record type {record_type}");
                }
            } else {
                panic!("Invalid: Variable passed to record set! is not a record type")
            }
        }
    }
}

fn compile_instrs_to_str(instr_vec: &[Instr]) -> String {
    const N_SPACES_INDENTATION: usize = 2;

    instr_vec
        .iter()
        .map(instr_to_str)
        .map(|s| format!("{}{}", " ".repeat(N_SPACES_INDENTATION), s))
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
        Instr::IAdd(v1, v2) => {
            let size_specifier = if let Val::Imm(_) = v2 { "qword " } else { "" };
            format!("add {size_specifier}{}, {}", val_to_str(v1), val_to_str(v2))
        }
        Instr::ISub(v1, v2) => {
            let size_specifier = if let Val::Imm(_) = v2 { "qword " } else { "" };
            format!("sub {size_specifier}{}, {}", val_to_str(v1), val_to_str(v2))
        }
        Instr::IMul(v1, v2) => format!("imul {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ITag(tag) => format!("{tag}:"),
        Instr::IJump(tag) => format!("jmp {tag}"),
        Instr::IJumpEqual(tag) => format!("je {tag}"),
        Instr::IJumpNotEqual(tag) => format!("jne {tag}"),
        Instr::IJumpLess(tag) => format!("jl {tag}"),
        Instr::ICmp(v1, v2) => {
            let size_specifier = if let Val::Imm(_) = v2 { "qword " } else { "" };
            format!("cmp {size_specifier}{}, {}", val_to_str(v1), val_to_str(v2))
        }
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
        Instr::IEnter(n) => format!("enter {}, 0", n),
        Instr::ILeave => "leave".to_string(),
        Instr::ISyscall => "int 0x80".to_string(),
    }
}

fn reg_to_str(r: &Reg) -> String {
    match r {
        Reg::RAX => "rax".to_string(),
        Reg::RSP => "rsp".to_string(),
        Reg::RDI => "rdi".to_string(),
        Reg::RSI => "rsi".to_string(),
        Reg::R10 => "r10".to_string(),
        Reg::R13 => "r13".to_string(),
        Reg::RBP => "rbp".to_string(),
        Reg::R11 => "r11".to_string(),
        Reg::R12 => "r12".to_string(),
        Reg::RBX => "rbx".to_string(),
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
    instr_vec: &mut Vec<Instr>,
    ctx: &mut CompileCtx,
    defns: &ProgDefns,
) -> ExprType {
    // Set up the function prologue for our_code_starts_here, we need `stack_space_needed`-many
    // bytes for local variables and expression evaluation, and need `rbx_storage_stack_space_needed`-many
    // bytes for pushing/popping $rbx
    let stack_space_needed_n_bytes = stack_space_needed(&func.body) +
        1 * SIZE_OF_DWORD +
        if func.signature.name == MAIN_FN_TAG {
            4 * SIZE_OF_DWORD
        } else { 0 };
    let rbx_storage_stack_space_needed_n_bytes = rbx_storage_stack_space_needed(&func.body);
    let total_stack_space_needed_n_bytes = stack_space_needed_n_bytes + rbx_storage_stack_space_needed_n_bytes;

    // Reset parts of the context (need to keep the tag_id as it was before)
    ctx.rbx_offset = if func.signature.name == MAIN_FN_TAG {
        -1 * 4 * SIZE_OF_DWORD
    } else {
        0
    };

    ctx.rbp_offset = -1 * rbx_storage_stack_space_needed_n_bytes + ctx.rbx_offset;
    ctx.scope.clear();

    instr_vec.push(
        Instr::IEnter(round_up_to_next_multiple_of_16(total_stack_space_needed_n_bytes))
    );
    
    for (i, arg) in func.signature.arg_types.iter().enumerate() {
        let arg_rbp_offset = i32::try_from(i + 2).unwrap() * SIZE_OF_DWORD;
        if let Some(_) = ctx.scope.insert(arg.0.clone(), (arg_rbp_offset, arg.1.clone())) {
            panic!("Invalid: duplicate parameter {} in function", arg.0);
        }
    }

    // if func.signature.name == MAIN_FN_TAG {
    //     // Store R12 so we can restore it later
    //     ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::R12);

    //     // Store current RBP to R12
    //     instr_vec.push(Instr::IMov(Val::Reg(Reg::R12), Val::Reg(Reg::RBP)));

    //     // Push max heap size to stack (can index with [rbp - 16])
    //     ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RSI);

    //     // Push current heap size (0) to stack (can index with [rbp - 24])
    //     ctx.rbp_offset = push_val_to_stack(instr_vec, ctx.rbp_offset, 0);

    //     // input: input to the program
    //     ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RDI);
    //     ctx.scope.insert("input".to_string(), (ctx.rbp_offset, ExprType::Number));
    // } else {
    //     // Build the variable scope starting with arguments
    //     for (i, arg) in func.signature.arg_types.iter().enumerate() {
    //         let arg_rbp_offset = i32::try_from(i + 2).unwrap() * SIZE_OF_DWORD;
    //         if let Some(_) = ctx.scope.insert(arg.0.clone(), (arg_rbp_offset, arg.1.clone())) {
    //             panic!("Invalid: duplicate parameter {} in function", arg.0);
    //         }
    //     }
    // }

    // Compile the function body
    let evaluated_return_type = if func.signature.name == MAIN_FN_TAG {
        println!("compiling main function, ctx.rbp_offset: {}, args len {}", ctx.rbp_offset, func.signature.arg_types.len());

        // Store R12 so we can restore it later
        let old_r12_rbp_offset = push_reg_to_stack(instr_vec, 0, Reg::R12);
        // Store current RBP to R12
        instr_vec.push(Instr::IMov(Val::Reg(Reg::R12), Val::Reg(Reg::RBP)));

        // Push max heap size to stack (can index with [rbp - 16])
        let max_heap_size_rbp_offset = push_reg_to_stack(instr_vec, old_r12_rbp_offset, Reg::RSI);

        // Push current heap size (0) to stack (can index with [rbp - 24])
        let curr_heap_size_rbp_offset = push_val_to_stack(instr_vec, max_heap_size_rbp_offset, 0);

        // Store RBX so we can restore it later
        let old_rbx_rbp_offset = push_reg_to_stack(instr_vec, curr_heap_size_rbp_offset, Reg::RBX);

        instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(0)));

        // input: input to the program
        ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RDI);
        ctx.scope.insert("input".to_string(), (ctx.rbp_offset, ExprType::Number));

        let ret = compile_to_instrs(&func.body, ctx, instr_vec, defns);

        // Call print function with final result if this is the main function
        if func.signature.name == MAIN_FN_TAG {
            instr_vec.push(Instr::IComment("Print final result".to_string()));
            instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RSI),
                Val::Imm(ret.to_type_flag()),
            ));

            // TODO @dkrajews: make this support printing records
            instr_vec.push(Instr::ICall("snek_print".to_string()));
        };

        // Restore RBX, R12
        instr_vec.extend(vec![
            Instr::IComment("Restore RBX, R12 after main fn body".to_string()),
            Instr::IMov(Val::Reg(Reg::RBX), Val::RegOffset(Reg::RBP, old_rbx_rbp_offset)),
            Instr::IMov(Val::Reg(Reg::R12), Val::RegOffset(Reg::RBP, old_r12_rbp_offset))
        ]);

        ret
    } else {
        let ret = compile_to_instrs(&func.body, ctx, instr_vec, defns);

        // Only try to decrement record arguments if there are any to avoid useless move instruction
        if func.signature.arg_types.iter().any(|(_, t)| matches!(t, ExprType::RecordPointer(_))) {
            let rax_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
            ctx.rbp_offset = rax_offset;

            for (i, arg) in func.signature.arg_types.iter().enumerate() {
                if let ExprType::RecordPointer(record_name) = &arg.1 {
                    // Decrement ref counter
                    let arg_rbp_offset = i32::try_from(i + 2).unwrap() * SIZE_OF_DWORD;
                    instr_vec.extend(vec![
                        Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::RBP, arg_rbp_offset)),
                        Instr::ICall(format!("{}_record_rc_decr", record_name)),
                    ]);
                }
            }
    
            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, rax_offset),
            ));   
        }

        ret
    };

    // if func.signature.name == MAIN_FN_TAG {
    //     ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RBX);
    //     instr_vec.push(Instr::IMov(, ()));
    // }
    // let evaluated_return_type = compile_to_instrs(&func.body, ctx, instr_vec, defns);

    // // Call print function with final result if this is the main function
    // if func.signature.name == MAIN_FN_TAG {
    //     instr_vec.push(Instr::IComment("Print final result".to_string()));
    //     instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
    //     instr_vec.push(Instr::IMov(
    //         Val::Reg(Reg::RSI),
    //         Val::Imm(evaluated_return_type.to_type_flag()),
    //     ));

    //     // TODO @dkrajews: make this support printing records
    //     instr_vec.push(Instr::ICall("snek_print".to_string()));
    // };

    instr_vec.extend(FUNCTION_EPILOGUE);

    // if func.signature.name == MAIN_FN_TAG {
    //     // Set carry forward assignment to be 0 at the very beginning
    //     // instr_vec.splice(1..1, vec![

    //     // ])
    //     // instr_vec.insert(1, Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(0)));
    // }
    evaluated_return_type
}

fn compile_record_rc_decr_function_to_instrs(
    instr_vec: &mut Vec<Instr>,
    record_name: &String,
    defns: &ProgDefns,
) {
    // Generates assembly to decrement the reference count of a record by 1, freeing the record if the refcount is 0
    // handles the case where the record has a pointer(s) to another record(s)
    
    let signature = defns
        .record_signatures
        .get(record_name)
        .expect("Record definition not found when trying to compile record rc decr");

    instr_vec.push(Instr::IEnter(16));
    let record_addr_offset = push_reg_to_stack(instr_vec, 0, Reg::RDI);

    // Perform null check on the record pointer
    instr_vec.extend(vec![
        Instr::ICmp(Val::Reg(Reg::RDI), Val::Imm(0)),
        Instr::IJumpEqual(format!("{}_record_rc_decr_end", signature.name)),
    ]);

    // Decrement the refcount by 1 and check if it hits zero
    instr_vec.extend(vec![
        Instr::IComment(format!("Decrement refcount by 1, compare to 0").to_string()),
        Instr::ISub(Val::RegOffset(Reg::RDI, 0), Val::Imm(1)),
        Instr::ICmp(Val::RegOffset(Reg::RDI, 0), Val::Imm(0)),
        Instr::IJumpNotEqual(format!("{}_record_rc_decr_end", signature.name)),
    ]);

    for (i, (field_name, field_type)) in signature.field_types.iter().enumerate() {
        if let ExprType::RecordPointer(field_record_type) = field_type {
            // If the field is a record pointer, we need to decrement the reference count of the field
            // and free the memory if the refcount is 0 recursively
            instr_vec.extend(vec![
                // Load the address of the record struct into R11
                Instr::IMov(
                    Val::Reg(Reg::R11),
                    Val::RegOffset(Reg::RBP, record_addr_offset),
                ),
                // Load the address of the field's pointer into RDI
                Instr::IMov(
                    Val::Reg(Reg::RDI),
                    Val::RegOffset(Reg::R11, i32::try_from(i + 1).unwrap() * SIZE_OF_DWORD),
                ),
                Instr::ICall(format!("{}_record_rc_decr", field_record_type)),
            ]);
        }
    }

    // Free the record struct's memory 
    instr_vec.extend(vec![
        Instr::IMov(
            Val::Reg(Reg::RDI),
            Val::RegOffset(Reg::RBP, record_addr_offset),
        ),
        Instr::ICall("free".to_string()), // Free the record struct
    ]);

    let n_bytes: i32 = calculate_record_size(signature);

    // Subtract from curr heap size
    instr_vec.push(Instr::ISub(Val::RegOffset(Reg::R12, CURRENT_HEAP_SIZE_R12_OFFSET), Val::Imm(n_bytes)));

    instr_vec.push(Instr::ITag(format!(
        "{}_record_rc_decr_end",
        signature.name
    )));

    instr_vec.extend(FUNCTION_EPILOGUE);









    // let smartptr_addr_rbp_offset: i32 = -8;

    // instr_vec.extend(vec![
    //     // Put the memory address on the stack
    //     Instr::IMov(
    //         Val::RegOffset(Reg::RBP, smartptr_addr_rbp_offset),
    //         Val::Reg(Reg::RDI),
    //     ),
    //     // Subtract 1 from ref count
    //     // Instr::ISub(Val::RegOffset(Reg::RDI, 0), Val::Imm(1)),
    // ]);

    // // let's first check if we are null
    // instr_vec.push(Instr::ICmp(Val::Reg(Reg::RDI), Val::Imm(0)));
    // instr_vec.push(Instr::IJumpEqual(format!(
    //     "{}_record_rc_decr_end",
    //     signature.name
    // )));

    // // Check all the fields of the record and see if any are pointers to other records
    // // instr_vec.push(Instr::IComment(format!("Check the record fields for other pointers").to_string()));

    // // for (i, (field_name, field_type)) in signature.field_types.iter().enumerate() {
    // //     if let ExprType::RecordPointer(field_record_type) = field_type {
    // //         // If the field is a record pointer, we need to decrement the reference count of the field
    // //         // and free the memory if the refcount is 0 recursively
    // //         instr_vec.extend(vec![
    // //             // Load the address of the record struct into R11
    // //             Instr::IMov(Val::Reg(Reg::R11), Val::RegOffset(Reg::RBP, smartptr_addr_rbp_offset)),
    // //             Instr::IMov(Val::Reg(Reg::R10), Val::RegOffset(Reg::R11, 1 * SIZE_OF_DWORD)),
    // //             // Load the address of the field's smart pointer into RDI
    // //             Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::R10, i32::try_from(i).unwrap() * SIZE_OF_DWORD)),
    // //             Instr::ICall(format!("{}_record_rc_decr", field_record_type))
    // //         ]);
    // //     }
    // // }

    // //              a    z
    // // x ----> 1 -> 2 -> 3 -> 4 -> 5

    // /*
    // fn refcount_decr(mem_addr_smart_ptr):
    //     if --mem_addr_smart_ptr[ref_cnt] > 0:
    //         return

    //     for each pointer field in record:
    //         refcount_decr(mem_addr_smart_ptr[field])

    //     free(mem_addr_smart_ptr[record_ptr])
    //     free(mem_addr_smart_ptr)

    // */

    // // Check if the refcount is 0 after decrementing/freeing/checking all the fields
    // instr_vec.push(Instr::IComment(
    //     format!("Check if the record needs to be freed").to_string(),
    // ));

    // instr_vec.extend(vec![
    //     Instr::IMov(
    //         Val::Reg(Reg::R12),
    //         Val::RegOffset(Reg::RBP, smartptr_addr_rbp_offset),
    //     ),
    //     // Subtract 1 from the smart pointer's refcount and check if it's now 0
    //     Instr::ISub(Val::RegOffset(Reg::R12, 0), Val::Imm(1)),
    //     Instr::ICmp(Val::RegOffset(Reg::R12, 0), Val::Imm(0)),
    //     Instr::IJumpNotEqual(format!("{}_record_rc_decr_end", signature.name)),
    //     // If the refcount is 0, free the memory
    // ]);

    // // assuming ref count is 0,
    // // check for other record pointers, if we have some, then decrement theiir ref count
    // for (i, (field_name, field_type)) in signature.field_types.iter().enumerate() {
    //     if let ExprType::RecordPointer(field_record_type) = field_type {
    //         // If the field is a record pointer, we need to decrement the reference count of the field
    //         // and free the memory if the refcount is 0 recursively
    //         instr_vec.extend(vec![
    //             // Load the address of the record struct into R11
    //             Instr::IMov(
    //                 Val::Reg(Reg::R11),
    //                 Val::RegOffset(Reg::RBP, smartptr_addr_rbp_offset),
    //             ),
    //             // Instr::IMov(Val::Reg(Reg::R10), Val::RegOffset(Reg::R11, 1 * SIZE_OF_DWORD)),
    //             // Load the address of the field's pointer into RDI
    //             Instr::IMov(
    //                 Val::Reg(Reg::RDI),
    //                 Val::RegOffset(Reg::R11, i32::try_from(i + 1).unwrap() * SIZE_OF_DWORD),
    //             ),
    //             Instr::ICall(format!("{}_record_rc_decr", field_record_type)),
    //         ]);
    //     }
    // }

    // // free memory
    // instr_vec.extend(vec![
    //     Instr::IMov(
    //         Val::Reg(Reg::RDI),
    //         Val::RegOffset(Reg::RBP, smartptr_addr_rbp_offset),
    //     ),
    //     Instr::ICall("free".to_string()), // Free the record struct
    // ]);

    // instr_vec.push(Instr::ITag(format!(
    //     "{}_record_rc_decr_end",
    //     signature.name
    // )));
    // instr_vec.extend(FUNCTION_EPILOGUE);
}

pub fn compile(p: &Prog, defns: &ProgDefns) -> String {
    // Compile all functions to instruction strings
    let mut asm_string: String = "extern snek_print
extern snek_error
extern malloc
extern free

section .text
global our_code_starts_here

out_of_memory_error:
  mov rdi, 4
  call snek_error

overflow_error:
  mov rdi, 3
  call snek_error

rc_incr:
  enter 0, 0
  ; Check if carry_forward_assignment is not set
  cmp rbx, 0
  je rc_incr_end
  ; Check if the pointer is null
  cmp rdi, 0
  je rc_incr_end
  ; Increment the ref count
  add qword [rdi], 1
  rc_incr_end:
  leave
  ret

"
    .to_string();

    let mut ctx: CompileCtx = CompileCtx {
        scope: VariableScope::new(),
        rbp_offset: 0,
        rbx_offset: 0,
        tag_id: 0,
    };

    // Auto-gen assembly for freeing records recursively
    for record_name in defns.record_signatures.keys() {
        let mut instr_vec: Vec<Instr> = Vec::new();
        compile_record_rc_decr_function_to_instrs(&mut instr_vec, record_name, defns);

        let asm_func_string = format!(
            "
{}:
{}
",
            format!("{}_record_rc_decr", record_name),
            compile_instrs_to_str(&instr_vec)
        );

        asm_string.push_str(&asm_func_string);
    }

    println!("Finished compiling free functions.");

    // Generate assembly for each function
    for func in p {
        println!("Starting compilation for {}", func.signature.name);
        let mut instr_vec: Vec<Instr> = Vec::new();
        let _func_return_type = compile_function_to_instrs(func, &mut instr_vec, &mut ctx, defns);

        let asm_func_string = format!(
            "
{}:
{}
",
            func.signature.name,
            compile_instrs_to_str(&instr_vec)
        );

        asm_string.push_str(&asm_func_string);
        println!("Finished compilation for {}", func.signature.name);
    }

    asm_string
}
