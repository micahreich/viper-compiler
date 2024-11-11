use core::panic;
use std::collections::HashSet;

use crate::types::*;

pub struct CompileCtx {
    pub scope: VariableScope,
    pub rbp_offset: i32,
    pub tag_id: i32,
    /// The `carry_fwd_assignment` flag is used to determine whether or not to increment the reference count of a record pointer
    /// depending on if the expression which is currently being evaluated is going to be assigned to a variable or not
    pub carry_fwd_assignment: bool,
}

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
    // We need to know how much stack space is needed to evaluate an expression; the mathematical
    // equation we need to satisfy is something like:
    // stack_space_needed(e) = sum ([ stack_space_needed(e_sub) for e_sub in evaluation of e ]) + DWORD_SIZE * # of calls to push_reg_to_stack

    match e {
        Expr::Boolean(_) | Expr::Number(_) | Expr::Id(_) => 0,
        Expr::UnOp(op1, e) => {
            match op1 {
                Op1::Print => {
                    // For print we need to push (1 value) RAX to the stack to save it before calling `snek_print`
                    SIZE_OF_DWORD + stack_space_needed(e)
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
            stack_space_needed(e1) + std::cmp::max(stack_space_needed(e2), stack_space_needed(e3))
        }
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
        Expr::Lookup(e1, _) => stack_space_needed(e1),
        Expr::RecordInitializer(_, fields) => {
            let mut space_needed = 0;
            for e in fields {
                space_needed += stack_space_needed(e);
            }

            // We need to allocate 2 additional dwords, 1 for the refcount pointer and
            // 1 for the raw record pointer

            space_needed
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
                if ctx.carry_fwd_assignment && matches!(e_type, ExprType::RecordPointer(_)) {
                    instr_vec.push(Instr::IAdd(Val::RegOffset(Reg::RAX, 0), Val::Imm(1)));
                }

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
            let e_type: ExprType = compile_to_instrs(e, ctx, instr_vec, defns);

            match op {
                Op1::Print => {
                    if let ExprType::RecordPointer(name) = &e_type {
                        todo!();
                        // let record_def = defns.record_signatures.get(name).expect("Record definition not found");
                        // // Let's first print the contents
                        // // if one of the contents is a pointer to another, we need to recursively call compile

                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Reg(Reg::RAX)));

                        // // print open parens
                        // instr_vec.push(Instr::IMov(
                        //     Val::Reg(Reg::RSI),
                        //     Val::Imm(5),
                        // ));

                        // // Move rsp to most recent stack-allocated local variable
                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
                        // instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(ctx.rbp_offset)));
                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

                        // // Align rsp to 16 bytes
                        // instr_vec.push(ALIGN_RSP_16_BYTES);

                        // instr_vec.push(Instr::ICall("snek_print".to_string()));

                        
                        // for (i, field_expr) in record_def.field_types.iter().enumerate() {        
                        //     instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::R10, i32::try_from(i).unwrap() * SIZE_OF_DWORD)));
                        //     instr_vec.push(Instr::IMov(
                        //         Val::Reg(Reg::RSI),
                        //         Val::Imm(field_expr.1.to_type_flag()),
                        //     ));

                        //     // Move rsp to most recent stack-allocated local variable
                        //     instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
                        //     instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(ctx.rbp_offset)));
                        //     instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

                        //     // Align rsp to 16 bytes
                        //     instr_vec.push(ALIGN_RSP_16_BYTES);

                        //     instr_vec.push(Instr::ICall("snek_print".to_string()));
                        // }


                        // instr_vec.push(Instr::IMov(
                        //     Val::Reg(Reg::RSI),
                        //     Val::Imm(6),
                        // ));

                        // // Move rsp to most recent stack-allocated local variable
                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
                        // instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(ctx.rbp_offset)));
                        // instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

                        // // Align rsp to 16 bytes
                        // instr_vec.push(ALIGN_RSP_16_BYTES);

                        // instr_vec.push(Instr::ICall("snek_print".to_string()));

                        // // Print statements should evaluate to the given value
                        // instr_vec.push(Instr::IMov(
                        //     Val::Reg(Reg::RAX),
                        //     Val::RegOffset(Reg::RBP, e_rbp_offset),
                        // ));
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
                Op2::Equal => {
                    match (e1_type, e2_type) {
                        (ExprType::RecordPointer(name1), ExprType::RecordPointer(name2)) => {
                            if name1 != name2 {
                                panic!("Type mismatch in equality comparison");
                            }
                        }
                        (ExprType::RecordPointer(_), ExprType::RecordNullPtr) => {},
                        (ExprType::RecordNullPtr, ExprType::RecordPointer(_)) => {},
                        (t1, t2) => {
                            if t1 != t2 {
                                panic!("Type mismatch in equality comparison");
                            }
                        }
                    }
                },
                _ => {
                    if e1_type != ExprType::Number || e2_type != ExprType::Number {
                        panic!("Invalid type for binary operation");
                    }
                }
            }

            // // Perform some type checking on the arguments
            // if !is_comparing_record_to_null && (*op == Op2::Equal && e1_type != e2_type) {
            //     panic!("Type mismatch in equality comparison");
            // } else if (*op != Op2::Equal)
            //     && !(e1_type == ExprType::Number && e2_type == ExprType::Number)
            // {
            //     panic!("Type mismatch for binary operation {:?}", op);
            // }

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
            let mut existing_identifiers: HashSet<String> = HashSet::new();
            let mut newly_created_variable_scope: VariableScope = VariableScope::new();
            let old_ctx_carry_fwd_assignment = ctx.carry_fwd_assignment;
            ctx.carry_fwd_assignment = true;

            for (var, var_e) in bindings {
                if var == "input" || !is_valid_identifier(var) {
                    panic!("Reserved keyword or invalid identifier used as variable name in let expression");
                }

                // Set the carry forward assignment flag to true for the bindings since we're doing assignments
                let var_e_type = compile_to_instrs(var_e, ctx, instr_vec, defns);

                if newly_created_variable_scope
                    .insert(var.clone(), (ctx.rbp_offset, var_e_type))
                    .is_some() {
                    panic!("Duplicate binding in let expression");
                }

                ctx.scope.insert(var.clone(), (ctx.rbp_offset, var_e_type));
            }

            ctx.carry_fwd_assignment = old_ctx_carry_fwd_assignment;

            // Compile the expression
            let e_type = compile_to_instrs(e, ctx, instr_vec, defns);
            
            // Check for any pointer types in the bindings and decrement the references
            for (var, (offset, e_type)) in newly_created_variable_scope.iter() {
                if let ExprType::RecordPointer(record_name) = e_type {
                    instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::RBP, *offset)));
                    instr_vec.push(Instr::ICall(format!("{}_record_rc_decr", record_name)));
                }
            }

            // Restore original scope after the let expression is finished
            ctx.scope = original_scope;

            e_type
        }
        Expr::Set(id, e1) => {
            // We're setting id = eval(e1), so we are assigning the evaluation result to id meaning
            // we need to carry forward the assignment flag

            let old_ctx_carry_fwd_assignment = ctx.carry_fwd_assignment;
            ctx.carry_fwd_assignment = true;

            let e1_type = compile_to_instrs(e1, ctx, instr_vec, defns);

            ctx.carry_fwd_assignment = old_ctx_carry_fwd_assignment;

            let (id_offset, id_type) = ctx.scope.get(id)
                .expect("Variable not found in scope during set expression");

            // If we're setting a record pointer, we need to decrement the reference count of the old value
            if let ExprType::RecordPointer(record_name) = id_type {
                instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::RBP, *id_offset)));
                instr_vec.push(Instr::ICall(format!("{}_record_rc_decr", record_name)));
            }
            
            instr_vec.push(Instr::IMov(
                Val::RegOffset(Reg::RBP, *id_offset),
                Val::Reg(Reg::RAX),
            ));

            e1_type
        }
        Expr::Block(expr_vec) => {
            let mut last_e_type: Option<ExprType> = None;

            let old_ctx_carry_fwd_assignment = ctx.carry_fwd_assignment;
            ctx.carry_fwd_assignment = false;

            for (i, e) in expr_vec.iter().enumerate() {
                // Since the block evalualtes to the last expression, we need to carry forward the assignment
                // if we're at the last expression in the block; otherwise we say it's false

                if i == expr_vec.len() - 1 {
                    ctx.carry_fwd_assignment = old_ctx_carry_fwd_assignment;
                }

                last_e_type = Some(compile_to_instrs(e, ctx, instr_vec, defns));
            }

            last_e_type.expect("Empty block expression")
        }
        Expr::If(e1, e2, e3) => {
            let curr_tag_id = ctx.tag_id;

            ctx.tag_id += 1;
            // Compile e1
            compile_to_instrs(e1, ctx, instr_vec, defns);

            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            // If e1 evaluates to false, go to e3
            instr_vec.push(Instr::IJumpEqual(format!("else{curr_tag_id}")));

            // Compile e2
            let return_type = compile_to_instrs(e2, ctx, instr_vec, defns);
            instr_vec.push(Instr::IJump(format!("end{curr_tag_id}")));

            // Compile e3
            instr_vec.push(Instr::ITag(format!("else{curr_tag_id}")));

            compile_to_instrs(e3, ctx, instr_vec, defns);

            instr_vec.push(Instr::IJump(format!("end{curr_tag_id}")));
            instr_vec.push(Instr::ITag(format!("end{curr_tag_id}")));

            return_type
        }
        Expr::RepeatUntil(e1, e2) => {
            let curr_tag_id = ctx.tag_id;

            ctx.tag_id += 1;
            // Do-while loop
            instr_vec.push(Instr::ITag(format!("loop{curr_tag_id}")));
            // Compile e1
            let return_type = compile_to_instrs(e1, ctx, instr_vec, defns);
            let rbp_offset_return = push_rax_to_stack(instr_vec, ctx.rbp_offset);
            ctx.rbp_offset = rbp_offset_return;

            // Compile e2
            compile_to_instrs(e2, ctx, instr_vec, defns);
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

            // TODO: need to check reference counts for this stuff

            let prev_rbp_offset = ctx.rbp_offset;

            let n_args = i32::try_from(args.len()).unwrap();
            let stack_space_to_align = round_up_to_next_multiple_of_16(n_args * SIZE_OF_DWORD);

            // Evaluate all the function arguments
            let mut evaluated_args_rbp_offsets: Vec<i32> = Vec::new();

            for arg_expr in args {
                let _arg_type =
                    compile_to_instrs(arg_expr, ctx, instr_vec, defns);
                let rbp_offset_arg = push_rax_to_stack(instr_vec, ctx.rbp_offset);
                ctx.rbp_offset = rbp_offset_arg;

                evaluated_args_rbp_offsets.push(rbp_offset_arg);
            }

            // Move rsp to most recent stack-allocated local variable
            instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
            instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(ctx.rbp_offset)));
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
                let rsp_offset = i32::try_from(i).unwrap() * SIZE_OF_DWORD; // positive offset from $rsp

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
            ctx.rbp_offset = prev_rbp_offset;

            func_sig.return_type.clone()
        }
        Expr::Lookup(e1, field) => {
            let e1_type = compile_to_instrs(e1, ctx, instr_vec, defns);

            if let ExprType::RecordPointer(record_name) = e1_type {
                let record_signature = defns.record_signatures.get(&record_name).unwrap();

                let field_index = record_signature
                    .field_types
                    .iter()
                    .position(|(field_name, _)| field_name == field);

                if let Some(idx) = field_index {
                    // The refcnt pointer is stored in rax after evaluating e1, so first dereference the second field to get the raw record pointer,
                    // then add the field offset to get the field value
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RAX),
                        Val::RegOffset(Reg::RAX, 1 * SIZE_OF_DWORD),
                    ));

                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RAX),
                        Val::RegOffset(Reg::RAX, i32::try_from(idx).unwrap() * SIZE_OF_DWORD),
                    ));

                    let return_type = record_signature.field_types[idx].1.clone();
                    if ctx.carry_fwd_assignment && matches!(return_type, ExprType::RecordPointer(_)) {
                        // Increment the reference count of the field
                        instr_vec.push(Instr::IAdd(Val::RegOffset(Reg::RAX, 0), Val::Imm(1)));
                    }

                    return_type
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
            // If this isn't going to be assigned to a variable, we can just ignore the result
            if !ctx.carry_fwd_assignment {
                return ExprType::RecordNullPtr;
            }

            // Move rsp to most recent stack-allocated local variable
            instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
            instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(ctx.rbp_offset)));
            instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

            // Align rsp to 16 bytes
            instr_vec.push(ALIGN_RSP_16_BYTES);

            // Any time we have a pointer, its storing an unsigned int ref_count and then the pointer
            // when we have a new record initializer, we first malloc space for the refcounted pointer,
            // then we malloc space for the record itself

            // Call malloc
            if let Some(record_signature) = defns.record_signatures.get(record_name) {
                // First malloc the reference counted pointer struct
                instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(REF_COUNT_PTR_SIZE as i32)));
                instr_vec.push(Instr::ICall("malloc".to_string()));
                instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
                instr_vec.push(Instr::IJumpEqual("null_pointer_error".to_string()));
            
                // Put a 1 in the reference count field
                instr_vec.push(Instr::IMov(Val::RegOffset(Reg::RAX, 0), Val::Imm(1)));

                // Store the record pointer on the stack temporarily
                let rbp_offset_refcnt_ptr_eval = push_rax_to_stack(instr_vec, ctx.rbp_offset);
                ctx.rbp_offset = rbp_offset_refcnt_ptr_eval;

                // Now allocate space for the record itself
                let n_bytes =
                    i32::try_from(record_signature.field_types.len() * SIZE_OF_DWORD as usize)
                        .expect("Record size in bytes exceeds i32 max value");
                instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(n_bytes)));

                // TODO @dkrajews: this will leak memory if this second malloc fails (should probably free the first malloc above before jumping to null_pointer_error)
                instr_vec.push(Instr::ICall("malloc".to_string()));
                instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
                instr_vec.push(Instr::IJumpEqual("null_pointer_error".to_string()));

                // Move rax into temporary stack place
                let rbp_offset_record_ptr_eval = push_rax_to_stack(instr_vec, ctx.rbp_offset);
                ctx.rbp_offset = rbp_offset_record_ptr_eval;
                
                // Initialize the rest of the fields
                for (i, field_expr) in fields.iter().enumerate() {
                    let field_type_eval = compile_to_instrs(field_expr, ctx, instr_vec, defns);

                    if field_type_eval != ExprType::RecordNullPtr
                        && field_type_eval != record_signature.field_types[i].1
                    {
                        panic!("Type mismatch in record initializer: ensure field type matches expression type, expected {:?} but got {:?}", record_signature.field_types[i].1, field_type_eval);
                    }
                    
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::R11),
                        Val::RegOffset(Reg::RBP, rbp_offset_record_ptr_eval),
                    ));

                    instr_vec.push(Instr::IMov(
                        Val::RegOffset(Reg::R11, i32::try_from(i).unwrap() * SIZE_OF_DWORD),
                        Val::Reg(Reg::RAX),
                    ));
                }

                // Move the refcount pointer back into rax
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RBP, rbp_offset_refcnt_ptr_eval),
                ));
                
                // Put the record pointer into the reference count object
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::R11),
                    Val::RegOffset(Reg::RBP, rbp_offset_record_ptr_eval),
                ));

                instr_vec.push(Instr::IMov(
                    Val::RegOffset(Reg::RAX, 1 * SIZE_OF_DWORD), // Skip the refcount field
                    Val::Reg(Reg::R11),
                ));

                ExprType::RecordPointer(record_signature.name.clone())
            } else {
                panic!(
                    "Invalid record initializer: record {} not found in definitions",
                    record_name
                );
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
        Instr::IAdd(v1, v2) => format!("add {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ISub(v1, v2) => format!("sub {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::IMul(v1, v2) => format!("imul {}, {}", val_to_str(v1), val_to_str(v2)),
        Instr::ITag(tag) => format!("{tag}:"),
        Instr::IJump(tag) => format!("jmp {tag}"),
        Instr::IJumpEqual(tag) => format!("je {tag}"),
        Instr::IJumpNotEqual(tag) => format!("jne {tag}"),
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
        Instr::IEnter(n) => format!("enter {}, 0", n),
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
        Reg::R12 => "r12".to_string(),
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
) -> ExprType {
    // Set up the function prologue for our_code_starts_here
    let stack_space_needed_n_bytes = stack_space_needed(&func.body)
        + if func.signature.name == MAIN_FN_TAG {
            SIZE_OF_DWORD
        } else {
            0
        };

    instr_vec.push(Instr::IEnter(round_up_to_next_multiple_of_16(
        stack_space_needed_n_bytes,
    )));

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
        rbp_offset = push_reg_to_stack(instr_vec, rbp_offset, Reg::RDI);
        scope.insert("input".to_string(), (rbp_offset, ExprType::Number));
    }

    // Compile the function body
    let evaluated_return_type =
        compile_to_instrs(&func.body, scope, instr_vec, &mut rbp_offset, tag_id);

    // Call print function with final result if this is the main function
    if func.signature.name == MAIN_FN_TAG {
        instr_vec.push(Instr::IComment("Print final result".to_string()));
        instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
        instr_vec.push(Instr::IMov(
            Val::Reg(Reg::RSI),
            Val::Imm(evaluated_return_type.to_type_flag()),
        ));

        // TODO @dkrajews: make this support printing records

        instr_vec.push(Instr::ICall("snek_print".to_string()));
    };

    instr_vec.extend(FUNCTION_EPILOGUE);
    func.signature.return_type
}

// fn compile_function_to_instrs(
//     func: &Function,
//     tag_id: &mut i32,
//     instr_vec: &mut Vec<Instr>,
//     defns: &ProgDefns,
// ) -> ExprType {
//     // Set up the function prologue for our_code_starts_here
//     instr_vec.push(Instr::IComment("Function prologue".to_string()));

//     instr_vec.extend(FUNCTION_PROLOGUE);

//     let scope = &mut VariableScope::new();
//     let mut rbp_offset = 0;

//     // Build the variable scope starting with arguments
//     let mut existing_identifiers: HashSet<String> = HashSet::new();

//     for (i, arg) in func.signature.arg_types.iter().enumerate() {
//         if existing_identifiers.contains(&arg.0) {
//             panic!("Duplicate param");
//         }
//         existing_identifiers.insert(arg.0.to_string());
//         let arg_rbp_offset = i32::try_from(i + 2).unwrap() * SIZE_OF_DWORD;
//         scope.insert(arg.0.clone(), (arg_rbp_offset, arg.1.clone()));
//     }

//     // Add `input` as a local variable if the function being parsed is main
//     if func.signature.name == MAIN_FN_TAG {
//         instr_vec.push(Instr::IPush(Val::Reg(Reg::RDI)));
//         rbp_offset -= SIZE_OF_DWORD;

//         scope.insert("input".to_string(), (rbp_offset, ExprType::Number));
//     }

//     // Compile the function body
//     instr_vec.push(Instr::IComment("Function body".to_string()));

//     let evaluated_return_type = compile_to_instrs(&func.body, scope, instr_vec, &mut rbp_offset, tag_id, defns);

//     // Call print function with final result if this is the main function
//     if func.signature.name == MAIN_FN_TAG {
//         instr_vec.push(Instr::IComment("Print final result".to_string()));
//         if let ExprType::RecordPointer(name) = &evaluated_return_type {
//             let record_def = defns.record_signatures.get(name).expect("Record definition not found");
//             // Let's first print the contents
//             // if one of the contents is a pointer to another, we need to recursively call compile

//             instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Reg(Reg::RAX)));

//             // print open parens
//             instr_vec.push(Instr::IMov(
//                 Val::Reg(Reg::RSI),
//                 Val::Imm(5),
//             ));

//             // Move rsp to most recent stack-allocated local variable
//             instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
//             instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(rbp_offset)));
//             instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

//             // Align rsp to 16 bytes
//             instr_vec.push(ALIGN_RSP_16_BYTES);

//             instr_vec.push(Instr::ICall("snek_print".to_string()));

            
//             for (i, field_expr) in record_def.field_types.iter().enumerate() {        
//                 instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::R10, i32::try_from(i).unwrap() * SIZE_OF_DWORD)));
//                 instr_vec.push(Instr::IMov(
//                     Val::Reg(Reg::RSI),
//                     Val::Imm(field_expr.1.to_type_flag()),
//                 ));

//                 // Move rsp to most recent stack-allocated local variable
//                 instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
//                 instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(rbp_offset)));
//                 instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

//                 // Align rsp to 16 bytes
//                 instr_vec.push(ALIGN_RSP_16_BYTES);

//                 instr_vec.push(Instr::ICall("snek_print".to_string()));
//             }


//             instr_vec.push(Instr::IMov(
//                 Val::Reg(Reg::RSI),
//                 Val::Imm(6),
//             ));

//             // Move rsp to most recent stack-allocated local variable
//             instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
//             instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(rbp_offset)));
//             instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));

//             // Align rsp to 16 bytes
//             instr_vec.push(ALIGN_RSP_16_BYTES);

//             instr_vec.push(Instr::ICall("snek_print".to_string()));
//         } else {
//             instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
//             instr_vec.push(Instr::IMov(
//                 Val::Reg(Reg::RSI),
//                 Val::Imm(evaluated_return_type.to_type_flag()),
//             ));
    
//             // Ensure 16-byte stack alignment prior to calling snek_print
    
//             // Move rsp to most recent stack-allocated local variable
//             instr_vec.push(Instr::IMov(Val::Reg(Reg::R11), Val::Reg(Reg::RBP)));
//             instr_vec.push(Instr::IAdd(Val::Reg(Reg::R11), Val::Imm(rbp_offset)));
//             instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::R11)));
    
//             instr_vec.push(ALIGN_RSP_16_BYTES);
//             instr_vec.push(Instr::ICall("snek_print".to_string()));
//         }
//         // instr_vec.push(Instr::IMov(Val::Reg(Reg::RSP), Val::Reg(Reg::RBX)));
//     };
//     instr_vec.push(Instr::IComment("Function epilogue".to_string()));
//     instr_vec.extend(FUNCTION_EPILOGUE);

//     func.signature.return_type.clone()
// }

fn compile_record_rc_decr_function_to_instrs(instr_vec: &mut Vec<Instr>, record_name: &String, defns: &ProgDefns) {
    // Generates assembly to decrement the reference count of a record by 1, freeing the record if the refcount is 0
    // handles the case where the record has a pointer to another record(s)

    // The memory layout for smart-pointers looks something like:
    // x (stack-allocated variable) •----(pointer)----> [refcount, record_ptr] (this is what we call the smart pointer)
    //                                                                 •----(record pointer)----> [field1, field2, ...]
    
    let signature = defns.record_signatures
        .get(record_name)
        .expect("Record definition not found when trying to compile record rc decr");

    instr_vec.push(Instr::IEnter(16));

    let smartptr_addr_rbp_offset = -8;
    instr_vec.extend(vec![
        // Put the memory address of the smart pointer on the stack
        Instr::IMov(Val::RegOffset(Reg::RBP, smartptr_addr_rbp_offset), Val::Reg(Reg::RDI)),
        // Check if the first argument (address of the smart pointer) is null
        Instr::ICmp(Val::Reg(Reg::RDI), Val::Imm(0)),
        Instr::IJumpEqual(format!("{}_record_rc_decr_end", signature.name))
    ]);
    
    // Check all the fields of the record and see if any are pointers to other records
    instr_vec.push(Instr::IComment(format!("Check the record fields for other pointers").to_string()));

    for (i, (field_name, field_type)) in signature.field_types.iter().enumerate() {
        if let ExprType::RecordPointer(field_record_type) = field_type {
            // If the field is a record pointer, we need to decrement the reference count of the field
            // and free the memory if the refcount is 0 recursively
            instr_vec.extend(vec![
                // Load the address of the record struct into R11
                Instr::IMov(Val::Reg(Reg::R11), Val::RegOffset(Reg::RBP, smartptr_addr_rbp_offset)),
                Instr::IMov(Val::Reg(Reg::R10), Val::RegOffset(Reg::R11, 1 * SIZE_OF_DWORD)),
                // Load the address of the field's smart pointer into RDI
                Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::R10, i32::try_from(i).unwrap() * SIZE_OF_DWORD)),
                Instr::ICall(format!("{}_record_rc_decr", field_record_type))
            ]);
        }
    }
    
    //              a    z
    // x ----> 1 -> 2 -> 3 -> 4 -> 5

    /*
    fn refcount_decr(mem_addr_smart_ptr):
        if --mem_addr_smart_ptr[ref_cnt] > 0:
            return
        
        for each pointer field in record:
            refcount_decr(mem_addr_smart_ptr[field])
        
        free(mem_addr_smart_ptr[record_ptr])
        free(mem_addr_smart_ptr)

    */

    // Check if the refcount is 0 after decrementing/freeing/checking all the fields
    instr_vec.push(Instr::IComment(format!("Check if the record needs to be freed").to_string()));

    instr_vec.extend(vec![
        Instr::IMov(Val::Reg(Reg::R12), Val::RegOffset(Reg::RBP, smartptr_addr_rbp_offset)),
        // Subtract 1 from the smart pointer's refcount and check if it's now 0
        Instr::ISub(Val::RegOffset(Reg::R12, 0), Val::Imm(1)),
        Instr::ICmp(Val::RegOffset(Reg::R12, 0), Val::Imm(0)),
        Instr::IJumpNotEqual(format!("{}_record_rc_decr_end", signature.name)),
        // If the refcount is 0, free the memory
        Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::R12, 1 * SIZE_OF_DWORD)),
        Instr::ICall("free".to_string()), // Free the record struct
        Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::R12)),
        Instr::ICall("free".to_string()), // Free the smart pointer
    ]);

    instr_vec.push(Instr::ITag(format!("{}_record_rc_decr_end", signature.name)));
    instr_vec.extend(FUNCTION_PROLOGUE);
}

pub fn compile(p: &Prog, defns: &ProgDefns) -> String {
    // Compile all functions to instruction strings
    let mut tag_id: i32 = 0;
    let mut asm_string: String = "extern snek_print
extern snek_error
extern malloc

section .text
global our_code_starts_here

null_pointer_error:
  mov rdi, 4
  call snek_error

overflow_error:
  mov rdi, 3
  call snek_error
"
    .to_string();

    // Auto-gen assembly for freeing records recursively
    for (record_name, record_signature) in defns.record_signatures.iter() {
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

    // Generate assembly for each function
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
