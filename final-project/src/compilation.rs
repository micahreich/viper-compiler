use core::panic;
use std::iter::zip;

use crate::types::*;

const N_SPACES_ASM_INDENTATION: usize = 2;

// Helper functions for simplifying common x86/stack behaviors
fn format_vtable_label(method_name: &String, method_class_owner_name: &String) -> String {
    format!("__{method_class_owner_name}_{method_name}")
}

fn format_stringified_heap_name(name: &String) -> String {
    format!("__{name}_heapobj_string")
}

fn place_args_in_rdi_rsi(instr_vec: &mut Vec<Instr>, rdi: Val, rsi: Val) {
    instr_vec.extend(vec![
        Instr::IMov(Val::Reg(Reg::RDI), rdi),
        Instr::IMov(Val::Reg(Reg::RSI), rsi),
    ]);
}

/// Push the value of a register to the stack at the given offset from RBP and return the new offset
fn push_reg_to_stack(instr_vec: &mut Vec<Instr>, rbp_offset: i32, reg: Reg) -> i32 {
    let new_rbp_offset = rbp_offset - SIZE_OF_DWORD;

    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RBP, new_rbp_offset),
        Val::Reg(reg),
    ));

    new_rbp_offset
}

/// Push an immediate value to the stack at the given offset from RBP and return the new offset
fn push_val_to_stack(instr_vec: &mut Vec<Instr>, rbp_offset: i32, val: i32) -> i32 {
    let new_rbp_offset = rbp_offset - SIZE_OF_DWORD;

    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RBP, new_rbp_offset),
        Val::Imm(val),
    ));

    new_rbp_offset
}

/// Push RBX to the RBX mini-stack at the given offset from RBP and return the new offset
fn push_rbx_to_stack(instr_vec: &mut Vec<Instr>, rbx_offset: i32) -> i32 {
    let new_rbx_offset = rbx_offset - SIZE_OF_DWORD;

    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RBP, new_rbx_offset),
        Val::Reg(Reg::RBX),
    ));

    new_rbx_offset
}

/// Pop RBX from the RBX mini-stack at the given offset from RBP and return the new offset
fn pop_rbx_from_stack(instr_vec: &mut Vec<Instr>, rbx_offset: i32) -> i32 {
    let new_rbx_offset = rbx_offset + SIZE_OF_DWORD;

    instr_vec.push(Instr::IMov(
        Val::Reg(Reg::RBX),
        Val::RegOffset(Reg::RBP, rbx_offset),
    ));

    new_rbx_offset
}

/// Set the carry forward assignment value in RBX to the given value
fn set_carry_forward(instr_vec: &mut Vec<Instr>, val: bool) {
    instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(i32::from(val))));
}

/// Push RBX to the stack and set the carry forward assignment value in RBX to the given value
fn push_rbx_and_set_carry_forward(instr_vec: &mut Vec<Instr>, rbx_offset: i32, val: bool) -> i32 {
    let new_rbx_offset = push_rbx_to_stack(instr_vec, rbx_offset);
    set_carry_forward(instr_vec, val);

    new_rbx_offset
}

/// Round a positive integer up to the next multiple of 16
fn round_up_to_next_multiple_of_16(n: i32) -> i32 {
    println!("Rounding up: {} to {}", n, (n + 15) & !15);
    (n + 15) & !15
}

/// Compute the amount of stack space needed to evaluate an expression
/// This is used to determine how much space to allocate on the stack for a given expression and
/// maintains the recursive invariant that the stack space needed for an expression is the sum of
/// the stack space needed for its subexpressions plus any extra space needed for the expression itself
fn stack_space_needed(e: &Expr) -> i32 {
    match e {
        Expr::Boolean(_) | Expr::Number(_) | Expr::Id(_) => 0,
        Expr::UnOp(op1, e) => {
            match op1 {
                Op1::Print => std::cmp::max(
                    stack_space_needed(e),
                    SIZE_OF_DWORD, // Space needed to temporarily store the result of the print call
                ),
                _ => stack_space_needed(e),
            }
        }
        Expr::BinOp(_, e1, e2) => {
            // For binary operations, we need to push the result of e2 to the stack
            std::cmp::max(
                SIZE_OF_DWORD + stack_space_needed(e1),
                stack_space_needed(e2),
            )
        }
        Expr::Let(bindings, e) => {
            // We push the evaluation of each binding to the stack
            let space_needed_for_bindings = SIZE_OF_DWORD * (bindings.len() as i32);
            let space_needed_for_bindings_eval =
                bindings
                    .iter()
                    .enumerate()
                    .fold(0, |acc, (i, (_, binding_expr))| {
                        std::cmp::max(
                            acc,
                            (i as i32 * SIZE_OF_DWORD) + stack_space_needed(binding_expr),
                        )
                    });

            std::cmp::max(space_needed_for_bindings, space_needed_for_bindings_eval)
                + std::cmp::max(
                    stack_space_needed(e),
                    SIZE_OF_DWORD, // Space needed to temporarily store body eval
                )
        }
        Expr::Set(_, e) => {
            std::cmp::max(
                stack_space_needed(e),
                SIZE_OF_DWORD, // Space needed to store evaluated RHS expression
            )
        }
        Expr::Block(expr_vec) => expr_vec
            .iter()
            .fold(0, |acc, e| std::cmp::max(acc, stack_space_needed(e))),
        Expr::If(e_cond, e_true, e_false) => {
            // We only end up needing stack space for evaluation or the TRUE or the
            // FALSE branch, not both
            std::cmp::max(
                stack_space_needed(e_cond),
                std::cmp::max(stack_space_needed(e_true), stack_space_needed(e_false)),
            )
        }
        Expr::RepeatUntil(e1, e2) => {
            // We need stack space for the evaluation of e1, e2, and 1 extra dword for
            // storing body evaluation result
            std::cmp::max(
                stack_space_needed(e1),
                SIZE_OF_DWORD + stack_space_needed(e2),
            )
        }
        Expr::Call(_, args) => {
            // We push all arguments to the function call onto the stack
            let space_needed_for_args_eval =
                args.iter().enumerate().fold(0, |acc, (i, arg_expr)| {
                    std::cmp::max(
                        acc,
                        (i as i32 * SIZE_OF_DWORD) + stack_space_needed(arg_expr),
                    )
                });

            space_needed_for_args_eval
        }
        Expr::Lookup(e1, _) => std::cmp::max(stack_space_needed(e1), 2 * SIZE_OF_DWORD),
        Expr::RecordInitializer(_, fields) => {
            let space_needed_for_fields_eval = fields
                .iter()
                .fold(0, |acc, e| std::cmp::max(acc, stack_space_needed(e)));

            space_needed_for_fields_eval + SIZE_OF_DWORD
        }
        Expr::SetField(_, _, expr) => std::cmp::max(stack_space_needed(expr), SIZE_OF_DWORD),
        Expr::ObjectInitializer(_, fields) => {
            let space_needed_for_fields_eval = fields
                .iter()
                .fold(0, |acc, e| std::cmp::max(acc, stack_space_needed(e)));

            space_needed_for_fields_eval + SIZE_OF_DWORD
        }
        Expr::CallMethod(_, _, args) => {
            let space_needed_for_args_eval =
                args.iter().enumerate().fold(0, |acc, (i, arg_expr)| {
                    std::cmp::max(
                        acc,
                        (i as i32 * SIZE_OF_DWORD) + stack_space_needed(arg_expr),
                    )
                });

            space_needed_for_args_eval
        }
    }
}

/// Compute the amount of stack space needed to evaluate an expression in terms of the
/// $rbx mini-stack which is used to store the carry forward assignment value
fn rbx_storage_stack_space_needed(e: &Expr) -> i32 {
    match e {
        Expr::Number(_)
        | Expr::Boolean(_)
        | Expr::Id(_)
        | Expr::UnOp(_, _)
        | Expr::BinOp(_, _, _) => 0,
        Expr::Let(bindings, expr) => {
            // We push the evaluation of each binding to the stack
            let space_needed_for_e = bindings.iter().fold(0, |acc, (_, binding_expr)| {
                std::cmp::max(acc, rbx_storage_stack_space_needed(binding_expr))
            });

            std::cmp::max(
                rbx_storage_stack_space_needed(expr),
                space_needed_for_e + SIZE_OF_DWORD,
            )
        }
        Expr::Set(_, expr) => {
            SIZE_OF_DWORD + rbx_storage_stack_space_needed(expr)
        }
        Expr::Block(expr_vec) => {
            let space_needed_for_block = expr_vec.iter().fold(0, |acc, e| {
                std::cmp::max(acc, rbx_storage_stack_space_needed(e))
            });

            space_needed_for_block + SIZE_OF_DWORD
        }
        Expr::If(expr_cond, expr_true, expr_false) => {
            let space_needed_for_branches = std::cmp::max(
                rbx_storage_stack_space_needed(expr_true),
                rbx_storage_stack_space_needed(expr_false),
            );

            std::cmp::max(
                SIZE_OF_DWORD + rbx_storage_stack_space_needed(expr_cond),
                space_needed_for_branches,
            )
        }
        Expr::RepeatUntil(expr_guard, expr_loop_body) => {
            std::cmp::max(
                rbx_storage_stack_space_needed(expr_loop_body),
                SIZE_OF_DWORD + rbx_storage_stack_space_needed(expr_guard),
            )
        }
        Expr::Call(_, args_vec) => {
            let space_needed_for_args = args_vec.iter().fold(0, |acc, e| {
                std::cmp::max(acc, rbx_storage_stack_space_needed(e))
            });

            space_needed_for_args + SIZE_OF_DWORD
        }
        Expr::Lookup(expr, _) => {
            rbx_storage_stack_space_needed(expr) + SIZE_OF_DWORD
        }
        Expr::RecordInitializer(_, _) => 0,
        Expr::SetField(_, _, expr) => {
            SIZE_OF_DWORD + rbx_storage_stack_space_needed(expr)
        }
        // TODO @mreich: technically carry forward will always be set to true in this AST block,
        // but should probably explicitly set it to 1 for clarity
        Expr::ObjectInitializer(_, _) => 0,
        Expr::CallMethod(_, _, args_vec) => {
            let space_needed_for_args = args_vec.iter().fold(0, |acc, e| {
                std::cmp::max(acc, rbx_storage_stack_space_needed(e))
            });

            space_needed_for_args + SIZE_OF_DWORD
        }
    }
}

/// Stringify an instruction to x86-64 assembly
fn instr_to_str(i: &Instr) -> String {
    match i {
        Instr::IMov(dst, src) => {
            let mut size_specifier = "";
            if matches!(src, Val::Imm(_)) || matches!(src, Val::LabelPointer(_)) {
                size_specifier = "qword ";
            }
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
        Instr::IRet => "ret".to_string(),
        Instr::IComment(s) => format!("; {}", s),
        Instr::IEnter(n) => format!("enter {}, 0", n),
        Instr::ILeave => "leave".to_string(),
        Instr::IDq(s) => format!("dq {}", s),
    }
}

/// Stringify a register to x86-64 assembly register name
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

/// Stringify a value to x86-64 assembly value
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
        Val::LabelPointer(s) => s.clone(),
    }
}

// Main compilation functions
fn compile_heap_allocated_initializer<T: HeapAllocated>(
    e: &T,
    fields: &Vec<Expr>,
    ctx: &mut CompileCtx,
    instr_vec: &mut Vec<Instr>,
    program: &Program,
) {
    ctx.tag_id += 1;
    let heap_initialize_end_tag = format!("heap_initialize_end{}", ctx.tag_id);

    // If this isn't going to be assigned to a variable, we can just ignore the result
    instr_vec.extend(vec![
        Instr::ICmp(Val::Reg(Reg::RBX), Val::Imm(0)),
        Instr::IJumpEqual(heap_initialize_end_tag.clone().into()),
    ]);

    // Now allocate space for the record itself
    let n_bytes = e.alloc_size();

    ctx.tag_id += 1;
    let heap_check_end_tag = format!("heap_check_end{}", ctx.tag_id);

    // Check if out of memory
    instr_vec.extend(vec![
        Instr::IAdd(
            Val::RegOffset(Reg::R12, CURRENT_HEAP_SIZE_R12_OFFSET),
            Val::Imm(n_bytes),
        ),
        Instr::IMov(
            Val::Reg(Reg::R11),
            Val::RegOffset(Reg::R12, CURRENT_HEAP_SIZE_R12_OFFSET),
        ),
        Instr::ICmp(
            Val::Reg(Reg::R11),
            Val::RegOffset(Reg::R12, MAX_HEAP_SIZE_R12_OFFSET),
        ),
        Instr::IJumpLess(heap_check_end_tag.clone().into()),
        Instr::ICall("out_of_memory_error".into()),
        Instr::ITag(heap_check_end_tag.into()),
    ]);

    // Allocate space for the item
    instr_vec.extend(vec![
        Instr::IMov(Val::Reg(Reg::RDI), Val::Imm(n_bytes)),
        Instr::ICall("malloc".into()),
        Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)),
        Instr::IJumpEqual("out_of_memory_error".into()),
    ]);

    // Move rax into temporary stack place
    let rbp_offset_ptr_eval = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
    ctx.rbp_offset = rbp_offset_ptr_eval;

    // Put a 1 in the reference count field
    instr_vec.push(Instr::IMov(Val::RegOffset(Reg::RAX, 0), Val::Imm(1)));

    for (i, (field_expr, field_data)) in zip(fields, e.field_types()).into_iter().enumerate() {
        let field_type_eval = compile_expr(field_expr, ctx, instr_vec, program);

        if !program.expr_a_subtypes_b(&field_type_eval, &field_data.1) {
            panic!(
                "Type mismatch in initializer for field {}: expected {:?} but got {:?}",
                field_data.0, field_data.1, field_type_eval
            );
        }

        instr_vec.extend(vec![
            Instr::IMov(
                Val::Reg(Reg::R11),
                Val::RegOffset(Reg::RBP, rbp_offset_ptr_eval),
            ),
            Instr::IMov(
                Val::RegOffset(Reg::R11, ((i as i32) + e.field_idx_start()) * SIZE_OF_DWORD),
                Val::Reg(Reg::RAX),
            ),
        ]);
    }

    // Move the pointer result back into rax
    instr_vec.push(Instr::IMov(
        Val::Reg(Reg::RAX),
        Val::RegOffset(Reg::RBP, rbp_offset_ptr_eval),
    ));

    instr_vec.push(Instr::ITag(heap_initialize_end_tag.into()));
}

fn compile_heap_allocated_set_field<T: HeapAllocated>(
    e: &T,
    id_offset: i32,
    rhs_field_name: &String,
    rhs_field_expr: &Expr,
    ctx: &mut CompileCtx,
    instr_vec: &mut Vec<Instr>,
    program: &Program,
) -> ExprType {
    let field_types = e.field_types();
    let field_index = field_types
        .iter()
        .position(|(field, _)| field == rhs_field_name);

    if let Some(idx) = field_index {
        // Evalulate the new field expression
        ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, true);
        let return_type_field_expr = compile_expr(rhs_field_expr, ctx, instr_vec, program);
        ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

        let rbp_offset_field_expr_eval = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
        ctx.rbp_offset = rbp_offset_field_expr_eval;

        let expected_return_type_field_expr = field_types[idx].1.clone();
        if return_type_field_expr != expected_return_type_field_expr {
            panic!("Invalid: set! on record for field does not match record signature,
                    expected {expected_return_type_field_expr:?} but got {return_type_field_expr:?}");
        }

        // Check if we're re-assigning to a RecordPointer field; if so, we must decrement the
        // refcount of the old field. We also need to check the carry forward flag to see if this set!
        // expression is being assigned to another variable

        if expected_return_type_field_expr.is_heap_allocated() {
            // Call rc_incr if we're doing something like var x = set! record_name field my_record(...) since
            // the set! expression returns the new field's value
            instr_vec.extend(vec![
                Instr::IMov(
                    Val::Reg(Reg::RDI),
                    Val::RegOffset(Reg::RBP, rbp_offset_field_expr_eval),
                ),
                Instr::ICall("rc_incr".into()),
            ]);

            let field_heap_allocated_type =
                expected_return_type_field_expr.extract_heap_allocated_type_name();

            // Decrement the reference count of the old value which was in this field
            instr_vec.extend(vec![
                Instr::IMov(Val::Reg(Reg::R11), Val::RegOffset(Reg::RBP, id_offset)),
                Instr::IMov(
                    Val::Reg(Reg::RDI),
                    Val::RegOffset(
                        Reg::R11,
                        ((idx as i32) + e.field_idx_start()) * SIZE_OF_DWORD,
                    ),
                ),
                Instr::ICall(format!("{}_record_rc_decr", field_heap_allocated_type).into()),
            ]);
        }

        // Put the new field value in place in memory
        instr_vec.extend(vec![
            Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, rbp_offset_field_expr_eval),
            ),
            Instr::IMov(Val::Reg(Reg::R11), Val::RegOffset(Reg::RBP, id_offset)),
            // Load the evaluated new field expression into memory at the field's location
            Instr::IMov(
                Val::RegOffset(
                    Reg::R11,
                    ((idx as i32) + e.field_idx_start()) * SIZE_OF_DWORD,
                ),
                Val::Reg(Reg::RAX),
            ),
        ]);

        expected_return_type_field_expr
    } else {
        panic!(
            "Invalid field lookup: field {rhs_field_name} not found in heap-allocated type {}",
            e.name()
        );
    }
}

fn compile_heap_allocated_lookup_field<T: HeapAllocated>(
    e: &T,
    field: &String,
    ctx: &mut CompileCtx,
    instr_vec: &mut Vec<Instr>,
) -> ExprType {
    let field_index = e
        .field_types()
        .iter()
        .position(|(field_name, _)| field_name == field);

    if let Some(idx) = field_index {
        instr_vec.push(Instr::IMov(
            Val::Reg(Reg::RAX),
            Val::RegOffset(
                Reg::RAX,
                ((idx as i32) + e.field_idx_start()) * SIZE_OF_DWORD,
            ),
        ));

        let field_eval_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
        ctx.rbp_offset = field_eval_offset;

        let return_type = e.field_types()[idx].1.clone();

        // Increment the ref count for the field if it's a record pointer
        if return_type.is_heap_allocated() {
            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RDI),
                Val::RegOffset(Reg::RBP, field_eval_offset),
            ));
            instr_vec.push(Instr::ICall("rc_incr".into()));
        }

        // // Decrement the ref count of the record pointer which we're looking up with
        // // after the temporary increment from earlier
        // instr_vec.extend(vec![
        //     Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::RBP, e1_addr_offset)),
        //     Instr::ICall(format!("{}_record_rc_decr", e.name())),
        // ]);

        // Move the evaluated field value into rax
        instr_vec.push(Instr::IMov(
            Val::Reg(Reg::RAX),
            Val::RegOffset(Reg::RBP, field_eval_offset),
        ));

        return_type
    } else {
        panic!(
            "Invalid field lookup: field {} not found in record/class {}",
            field,
            e.name()
        );
    }
}

fn compile_function_arguments(
    args: &Vec<Expr>,
    ctx: &mut CompileCtx,
    instr_vec: &mut Vec<Instr>,
    program: &Program,
    argument_rsp_offset: i32,
) {
    // Track the old carry forward assignment value, temporarily set to 1 for arguments
    ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, true);

    for (i, arg_expr) in args.iter().enumerate() {
        let _arg_type = compile_expr(arg_expr, ctx, instr_vec, program);

        // Push the evaluated arguments onto the stack in the correct order, using the
        // following ordering convention:
        // [arg 4] 0x20
        // [arg 3] 0x18
        // [arg 2] 0x10
        // [arg 1] 0x08 <- $rsp

        instr_vec.push(Instr::IMov(
            Val::RegOffset(Reg::RSP, ((i as i32) + argument_rsp_offset) * SIZE_OF_DWORD),
            Val::Reg(Reg::RAX),
        ));
    }

    // Cut off david's balls and put them in a jar and then put them in a jar and also put them in a jar
    ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);
}

/// Compile an expression to a vector of x86-64 assembly instructions
fn compile_expr(
    e: &Expr,
    ctx: &mut CompileCtx,
    instr_vec: &mut Vec<Instr>,
    program: &Program,
) -> ExprType {
    let rbp_offset_pre_eval = ctx.rbp_offset;

    let e_type = match e {
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
                if e_type.is_heap_allocated() {
                    instr_vec.extend(vec![
                        Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)),
                        Instr::ICall("rc_incr".into()),
                    ]);
                }

                e_type.clone()
            }
            None => {
                if s == "NULL" {
                    instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));
                    ExprType::NullPtr
                } else {
                    panic!("Invalid: Unbound variable identifier {s}");
                }
            }
        },
        Expr::UnOp(op, e) => {
            let e_type = compile_expr(e, ctx, instr_vec, program);

            match op {
                Op1::Print => {
                    let e_rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                    ctx.rbp_offset = e_rbp_offset;

                    if e_type.is_heap_allocated() {
                        let e_type_name = e_type.extract_heap_allocated_type_name();
                        instr_vec.extend(vec![
                            Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)),
                            Instr::ICall(format!("{}_print", e_type_name).into()),
                        ]);
                    } else {
                        place_args_in_rdi_rsi(
                            instr_vec,
                            Val::Reg(Reg::RAX),
                            Val::Imm(e_type.to_type_flag()),
                        );

                        instr_vec.push(Instr::ICall("snek_print".into()));
                        instr_vec.extend(PRINT_NEWLINE);
                    }

                    // Print statements should evaluate to the given printed value
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RAX),
                        Val::RegOffset(Reg::RBP, e_rbp_offset),
                    ));

                    // if let ExprType::RecordPointer(name) = &e_type {
                    //     let e_rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                    //     ctx.rbp_offset = e_rbp_offset;

                    //     let record_def = program
                    //         .records
                    //         .get(name)
                    //         .expect("Record definition not found");

                    //     instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Reg(Reg::RAX)));

                    //     compile_heap_allocated_print(&record_def.field_types, instr_vec, 1);

                    //     // // Print statements should evaluate to the given value
                    //     instr_vec.push(Instr::IMov(
                    //         Val::Reg(Reg::RAX),
                    //         Val::RegOffset(Reg::RBP, e_rbp_offset),
                    //     ));
                    // } else if let ExprType::ObjectPointer(name) = &e_type {
                    //     let e_rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                    //     ctx.rbp_offset = e_rbp_offset;

                    //     let class_def = program
                    //         .classes
                    //         .get(name)
                    //         .expect("Record definition not found");

                    //     instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Reg(Reg::RAX)));

                    //     compile_heap_allocated_print(&class_def.field_types, instr_vec, 2);

                    //     // // Print statements should evaluate to the given value
                    //     instr_vec.push(Instr::IMov(
                    //         Val::Reg(Reg::RAX),
                    //         Val::RegOffset(Reg::RBP, e_rbp_offset),
                    //     ));
                    // } else {
                    //     let e_rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                    //     ctx.rbp_offset = e_rbp_offset;

                    //     instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
                    //     instr_vec.push(Instr::IMov(
                    //         Val::Reg(Reg::RSI),
                    //         Val::Imm(e_type.to_type_flag()),
                    //     ));

                    //     instr_vec.push(Instr::ICall("snek_print".to_string()));

                    //     // Print statements should evaluate to the given printed value
                    //     instr_vec.push(Instr::IMov(
                    //         Val::Reg(Reg::RAX),
                    //         Val::RegOffset(Reg::RBP, e_rbp_offset),
                    //     ));
                    // }
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

                    instr_vec.push(Instr::IJumpOverflow("overflow_error".into()));
                }
            };

            e_type
        }
        Expr::BinOp(op, e1, e2) => {
            // Compile e2 first so that subtraction works nicely, leaves e1 in rax
            let e2_type = compile_expr(e2, ctx, instr_vec, program);
            let rbp_offset_e2_eval = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
            ctx.rbp_offset = rbp_offset_e2_eval;

            // Then compile e1, which will be left in rax
            let e1_type = compile_expr(e1, ctx, instr_vec, program);

            match op {
                Op2::Equal => {
                    if !program.expr_a_subtypes_b(&e1_type, &e2_type) {
                        panic!(
                            "Type mismatch in equality comparison, expected {e1_type:?} but got {e2_type:?}"
                        );
                    }
                }
                _ => {
                    if e1_type != ExprType::Number || e2_type != ExprType::Number {
                        panic!("Invalid type for binary operation");
                    }
                }
            }

            let ret_type = if matches!(
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

                instr_vec.push(Instr::IJumpOverflow("overflow_error".into()));
                ExprType::Number
            } else {
                panic!("Invalid binary operation {:?}", op);
            };

            ret_type
        }
        Expr::Let(bindings, e) => {
            instr_vec.push(Instr::IComment("Let expression".into()));
            let original_scope = ctx.scope.clone();

            // Add the bindings from the scope
            let mut newly_created_variable_scope: VariableScope = VariableScope::new();

            // Track the old carry forward assignment value, temporarily set to 1 for let bindings
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, true);

            for (var_name, var_e) in bindings {
                let var_e_type = compile_expr(var_e, ctx, instr_vec, program);

                // Save the evaluated value of the variable on the stack
                ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);

                if newly_created_variable_scope
                    .insert(var_name.clone(), (ctx.rbp_offset, var_e_type.clone()))
                    .is_some()
                {
                    panic!("Duplicate binding in let expression");
                } else {
                    ctx.scope
                        .insert(var_name.clone(), (ctx.rbp_offset, var_e_type.clone()));
                }
            }

            ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

            // Compile the expression
            let e_type = compile_expr(e, ctx, instr_vec, program);
            ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);

            // Check for any pointer types in the bindings and decrement the references
            for (_var_name, (offset, e_type)) in newly_created_variable_scope.iter() {
                if e_type.is_heap_allocated() {
                    instr_vec.push(Instr::IMov(
                        Val::Reg(Reg::RDI),
                        Val::RegOffset(Reg::RBP, *offset),
                    ));
                    instr_vec.push(Instr::ICall(
                        format!(
                            "{}_record_rc_decr",
                            e_type.extract_heap_allocated_type_name()
                        )
                        .into(),
                    ));
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
            let (id_offset, id_type) = ctx
                .scope
                .get(id)
                .expect("Variable not found in scope during set expression")
                .clone();

            if id_type.is_heap_allocated() {
                let type_name = id_type.extract_heap_allocated_type_name();

                ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, true);
                let e1_type = compile_expr(e1, ctx, instr_vec, program);
                ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

                if e1_type != id_type {
                    panic!(
                        "Type mismatch in set! expression, expected {id_type:?} but got {e1_type:?}"
                    );
                }

                let e1_eval_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
                ctx.rbp_offset = e1_eval_offset;

                // Decrement the refcount of what `id` was originally pointing to
                instr_vec.extend(vec![
                    Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::RBP, id_offset)),
                    Instr::ICall(format!("{}_record_rc_decr", type_name).into()),
                ]);

                // Move the evaluated value of e1 back into rax
                instr_vec.extend(vec![
                    Instr::IComment(format!("Move evaluated value of e1 into place of {}", id).into()),
                    Instr::IMov(Val::Reg(Reg::RAX), Val::RegOffset(Reg::RBP, e1_eval_offset)),
                ]);
            } else {
                // TODO @dkrajews, @mreich: do we need to set rbx = 0 explicitly here?
                let e1_type = compile_expr(e1, ctx, instr_vec, program);

                if e1_type != id_type {
                    panic!(
                        "Type mismatch in set! expression, expected {id_type:?}, got {e1_type:?}"
                    );
                }
            }

            instr_vec.extend(vec![
                Instr::IComment(format!("Move evaluated value of e1 into place of {}", id).into()),
                Instr::IMov(Val::RegOffset(Reg::RBP, id_offset), Val::Reg(Reg::RAX)),
            ]);

            id_type.clone()
        }
        Expr::Block(expr_vec) => {
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, false);

            for (i, e) in expr_vec.iter().enumerate() {
                if i == expr_vec.len() - 1 {
                    // Since the block evalualtes to the last expression, we need to carry forward the assignment
                    // if we're at the last expression in the block; otherwise we say it's false
                    ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);
                    let ret_type = compile_expr(e, ctx, instr_vec, program);

                    return ret_type;
                } else {
                    compile_expr(e, ctx, instr_vec, program);
                }
            }

            panic!("Invalid: Empty block expression encountered");
        }
        Expr::If(e_condition, e_true, e_false) => {
            let if_stmt_tag_id = ctx.tag_id;
            ctx.tag_id += 1;

            // Compile e1 (if condition)
            // Track the old carry forward assignment value, temporarily set to 0 for if condition
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, false);
            compile_expr(e_condition, ctx, instr_vec, program);
            ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

            let rbp_starting_offset_from_condition = ctx.rbp_offset;
            let rbx_starting_offset_from_condition = ctx.rbx_offset;

            // If e1 evaluates to false, go to e3 (false branch)
            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            instr_vec.push(Instr::IJumpEqual(format!("else{if_stmt_tag_id}").into()));

            // Compile e2 (true branch)
            let return_type_true_branch = compile_expr(e_true, ctx, instr_vec, program);
            instr_vec.push(Instr::IJump(format!("end{if_stmt_tag_id}").into()));

            // Compile e3 (false branch)
            ctx.rbp_offset = rbp_starting_offset_from_condition;
            ctx.rbx_offset = rbx_starting_offset_from_condition;

            instr_vec.push(Instr::ITag(format!("else{if_stmt_tag_id}").into()));
            let return_type_false_branch = compile_expr(e_false, ctx, instr_vec, program);

            if return_type_true_branch != return_type_false_branch {
                panic!("Type mismatch in if-else branches, got {return_type_true_branch:?} and {return_type_false_branch:?}");
            }

            instr_vec.push(Instr::ITag(format!("end{if_stmt_tag_id}").into()));

            return_type_true_branch
        }
        Expr::RepeatUntil(e1, e2) => {
            let loop_tag_id = ctx.tag_id;
            ctx.tag_id += 1;

            instr_vec.push(Instr::ITag(format!("loop{loop_tag_id}").into()));

            // Compile e1 (loop body)
            let return_type_loop_body = compile_expr(e1, ctx, instr_vec, program);
            let rbp_offset_loop_body_e = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
            ctx.rbp_offset = rbp_offset_loop_body_e;

            // Compile e2 (loop condition)
            // Track the old carry forward assignment value, temporarily set to 0 for loop guard
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, false);
            compile_expr(e2, ctx, instr_vec, program);
            ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

            // If e2 returned false, jump back to top of loop
            instr_vec.extend(vec![
                Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)),
                Instr::IJumpEqual(format!("loop{loop_tag_id}").into()),
            ]);

            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RBP, rbp_offset_loop_body_e),
            ));

            return_type_loop_body
        }
        Expr::Call(func_name, args) => {
            instr_vec.push(Instr::IComment("Call expression".into()));

            let func = program
                .functions
                .get(func_name)
                .expect("Function {func_name} not found");
            if args.len() != func.arg_types.len() {
                panic!(
                    "Invalid number of arguments for function call {func_name}, expected {} but got {}",
                    func.arg_types.len(), args.len()
                );
            }

            compile_function_arguments(args, ctx, instr_vec, program, 0);

            // Call the function
            instr_vec.push(Instr::ICall(func_name.clone().into()));

            func.return_type.clone()
        }
        Expr::Lookup(e1, field) => {
            instr_vec.push(Instr::IComment("Lookup expression".into()));
            // Track the old carry forward assignment value, temporarily set to 0 for field lookup
            ctx.rbx_offset = push_rbx_and_set_carry_forward(instr_vec, ctx.rbx_offset, false);
            let e1_type = compile_expr(e1, ctx, instr_vec, program);
            ctx.rbx_offset = pop_rbx_from_stack(instr_vec, ctx.rbx_offset);

            let e1_addr_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
            ctx.rbp_offset = e1_addr_offset;

            if let ExprType::RecordPointer(record_name) = e1_type {
                let record = program
                    .records
                    .get(&record_name)
                    .expect("Record definition not found.");
                compile_heap_allocated_lookup_field(record, field, ctx, instr_vec)
            } else if let ExprType::ObjectPointer(object_name) = e1_type {
                let object = program
                    .classes
                    .get(&object_name)
                    .expect("Object definition not found.");
                compile_heap_allocated_lookup_field(object, field, ctx, instr_vec)
            } else {
                panic!("Invalid lookup expression, must be a non-null record or class pointer");
            }
        }
        Expr::RecordInitializer(record_name, fields) => {
            instr_vec.push(Instr::IComment(format!(
                "Begin record initialization for record type {record_name}",
            ).into()));

            let signature = program
                .records
                .get(record_name)
                .expect("Record signature not found");

            if fields.len() != signature.field_types.len() {
                panic!(
                    "Invalid number of fields in record initializer for record type {record_name}, expected {} but got {}",
                    signature.field_types.len(), fields.len()
                );
            }

            compile_heap_allocated_initializer(signature, fields, ctx, instr_vec, program);

            instr_vec.push(Instr::IComment(format!(
                "End record initialization for record type {record_name}",
            ).into()));

            ExprType::RecordPointer(record_name.clone())
        }
        Expr::SetField(id, field_name, field_expr) => {
            let (id_offset, id_type) = ctx
                .scope
                .get(id)
                .expect("Variable not found in scope during set expression")
                .clone();

            match &id_type {
                ExprType::RecordPointer(record_name) => {
                    let record_signature = program.records.get(record_name).unwrap();

                    let field_type = compile_heap_allocated_set_field(
                        record_signature,
                        id_offset,
                        field_name,
                        field_expr,
                        ctx,
                        instr_vec,
                        program,
                    );

                    field_type
                }
                ExprType::ObjectPointer(class_name) => {
                    let class_signature = program.classes.get(class_name).unwrap();

                    let field_type = compile_heap_allocated_set_field(
                        class_signature,
                        id_offset,
                        field_name,
                        field_expr,
                        ctx,
                        instr_vec,
                        program,
                    );

                    field_type
                }
                _ => panic!("Invalid: set! with fields on non-heap-allocated type"),
            }
        }
        Expr::ObjectInitializer(class_name, fields) => {
            instr_vec.push(Instr::IComment(format!(
                "Begin initialization for object type {class_name}",
            ).into()));

            let class = program
                .classes
                .get(class_name)
                .expect("Record signature not found");

            if fields.len() != class.field_types.len() {
                panic!(
                    "Invalid number of fields in object initializer for object type {class_name}, expected {} but got {}",
                    class.field_types.len(), fields.len()
                );
            }

            compile_heap_allocated_initializer(class, fields, ctx, instr_vec, program);

            // We have to put the VTable pointer in index 1 of the object
            let vtable_ptr_label = format!("{}_VTable", class_name);
            instr_vec.push(Instr::IMov(
                Val::RegOffset(Reg::RAX, 1 * SIZE_OF_DWORD),
                Val::LabelPointer(vtable_ptr_label),
            ));

            instr_vec.push(Instr::IComment(format!(
                "End object initialization for object type {class_name}",
            ).into()));

            ExprType::ObjectPointer(class_name.clone())
        }
        Expr::CallMethod(obj_id, method_name, args) => {
            // Compile first argument and ensure it points to an object
            let (_, obj_id_type) = ctx
                .scope
                .get(obj_id)
                .expect("Class not found in scope during set expression")
                .clone();

            if let ExprType::ObjectPointer(class_name) = obj_id_type {
                let class_signature = program
                    .classes
                    .get(&class_name)
                    .expect("Class definition not found");

                let (vtable_idx, owning_class_name) = class_signature.vtable_indices
                    .get(method_name)
                    .expect("Method definition {method_name} not found in vtable for class {class_name}");

                // Search for method in class definition
                let method_signature = program
                    .classes
                    .get(owning_class_name)
                    .expect("Class definition not found for {owning_class_name}")
                    .methods
                    .get(method_name)
                    .expect(
                        "Method {method_name} definition not found in class {owning_class_name}",
                    );

                // `self` has been inserted into the arguments suring parsing
                if args.len() != method_signature.arg_types.len() {
                    panic!("Invalid number of arguments for method call {method_name} on object of type {class_name}, expected {} but got {}",
                    method_signature.arg_types.len(), args.len());
                }

                compile_function_arguments(args, ctx, instr_vec, program, 0);

                // Grab method (function pointer) from vtable and call it
                instr_vec.extend(vec![
                    Instr::IMov(
                        Val::Reg(Reg::R11),
                        Val::LabelPointer(format!(
                            "[{}_VTable+{}]",
                            class_name,
                            (*vtable_idx as i32) * SIZE_OF_DWORD
                        )),
                    ),
                    Instr::ICall(reg_to_str(&Reg::R11).into()),
                ]);
                
                method_signature.return_type.clone()
            } else {
                panic!("Cannot call method on a non-object");
            }
        }
    };

    ctx.rbp_offset = rbp_offset_pre_eval;
    e_type
}

/// Convert a vector of instructions to a string
fn compile_instrs_to_str(instr_vec: &[Instr]) -> String {
    instr_vec
        .iter()
        .map(instr_to_str)
        .map(|s| format!("{}{}", " ".repeat(N_SPACES_ASM_INDENTATION), s))
        .collect::<Vec<String>>()
        .join("\n")
}

/// Convert a function body to a vector of instructions, including all necessary prologue and epilogue
/// instructions and storage of any callee-saved registers
fn compile_function_to_instrs(
    func: &Function,
    instr_vec: &mut Vec<Instr>,
    ctx: &mut CompileCtx,
    program: &Program,
) -> ExprType {
    // Set up the function prologue for our_code_starts_here, we need `stack_space_needed`-many
    // bytes for local variables and expression evaluation, and need `rbx_storage_stack_space_needed`-many
    // bytes for pushing/popping $rbx
    let stack_space_needed_n_bytes = stack_space_needed(&func.body) + 1 * SIZE_OF_DWORD;
    let rbx_storage_stack_space_needed_n_bytes = rbx_storage_stack_space_needed(&func.body);
    let total_stack_space_needed_n_bytes =
        stack_space_needed_n_bytes + rbx_storage_stack_space_needed_n_bytes;

    // Reset parts of the context (need to keep the tag_id as it was before)
    ctx.rbx_offset = 0;
    ctx.rbp_offset = ctx.rbx_offset - rbx_storage_stack_space_needed_n_bytes;
    ctx.scope.clear();

    instr_vec.push(Instr::IEnter(round_up_to_next_multiple_of_16(
        total_stack_space_needed_n_bytes,
    )));

    for (i, arg) in func.arg_types.iter().enumerate() {
        let arg_rbp_offset = i32::try_from(i + 2).unwrap() * SIZE_OF_DWORD;
        if ctx
            .scope
            .insert(arg.0.clone(), (arg_rbp_offset, arg.1.clone()))
            .is_some()
        {
            panic!("Invalid: duplicate parameter {} in function", arg.0);
        }
    }

    // Compile the function body
    let ret = compile_expr(&func.body, ctx, instr_vec, program);

    // Only try to decrement record arguments if there are any to avoid useless move instruction
    if func.arg_types.iter().any(|(_, t)| {
        matches!(t, ExprType::RecordPointer(_)) || matches!(t, ExprType::ObjectPointer(_))
    }) {
        let rax_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RAX);
        ctx.rbp_offset = rax_offset;

        for (i, arg) in func.arg_types.iter().enumerate() {
            if arg.1.is_heap_allocated() {
                // Decrement ref counter
                let arg_rbp_offset = i32::try_from(i + 2).unwrap() * SIZE_OF_DWORD;
                instr_vec.extend(vec![
                    Instr::IMov(Val::Reg(Reg::RDI), Val::RegOffset(Reg::RBP, arg_rbp_offset)),
                    Instr::ICall(format!(
                        "{}_record_rc_decr",
                        arg.1.extract_heap_allocated_type_name()
                    ).into()),
                ]);
            }
        }

        instr_vec.push(Instr::IMov(
            Val::Reg(Reg::RAX),
            Val::RegOffset(Reg::RBP, rax_offset),
        ));
    }

    instr_vec.extend(FUNCTION_EPILOGUE);

    ret
}

fn compile_main_expr_to_instrs(
    expr: &Box<Expr>,
    instr_vec: &mut Vec<Instr>,
    ctx: &mut CompileCtx,
    program: &Program,
) -> ExprType {
    // Set up the function prologue for our_code_starts_here, we need `stack_space_needed`-many
    // bytes for local variables and expression evaluation, and need `rbx_storage_stack_space_needed`-many
    // bytes for pushing/popping $rbx
    let stack_space_needed_n_bytes = stack_space_needed(expr) + 5 * SIZE_OF_DWORD;

    let rbx_storage_stack_space_needed_n_bytes = rbx_storage_stack_space_needed(expr);
    let total_stack_space_needed_n_bytes =
        stack_space_needed_n_bytes + rbx_storage_stack_space_needed_n_bytes;

    // Reset parts of the context (need to keep the tag_id as it was before)
    ctx.rbx_offset = -1 * 4 * SIZE_OF_DWORD;
    ctx.rbp_offset = ctx.rbx_offset - rbx_storage_stack_space_needed_n_bytes;
    ctx.scope.clear();

    instr_vec.push(Instr::IEnter(round_up_to_next_multiple_of_16(
        total_stack_space_needed_n_bytes,
    )));

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

    // Set initial carry forward to 0
    instr_vec.push(Instr::IMov(Val::Reg(Reg::RBX), Val::Imm(0)));

    // input: input to the program
    ctx.rbp_offset = push_reg_to_stack(instr_vec, ctx.rbp_offset, Reg::RDI);
    ctx.scope
        .insert("input".to_string(), (ctx.rbp_offset, ExprType::Number));

    let ret = compile_expr(expr, ctx, instr_vec, program);

    // Call print function with final result
    instr_vec.push(Instr::IComment("Print final result".into()));
    if ret.is_heap_allocated() {
        let type_name = ret.extract_heap_allocated_type_name();
        let stringified_name_label = format_stringified_heap_name(&type_name);

        instr_vec.extend(vec![
            Instr::IMov(
                Val::Reg(Reg::RSI),
                Val::Imm(ExprType::RecordPointer("".into()).to_type_flag()),
            ),
            Instr::IMov(
                Val::Reg(Reg::R11),
                Val::Imm(ExprType::NullPtr.to_type_flag()),
            ),
            Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)),
            Instr::ICMovEqual(Val::Reg(Reg::RSI), Val::Reg(Reg::R11)),
            Instr::IMov(
                Val::Reg(Reg::RDI),
                Val::LabelPointer(stringified_name_label),
            ),
        ]);
    } else {
        instr_vec.extend(vec![
            Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)),
            Instr::IMov(Val::Reg(Reg::RSI), Val::Imm(ret.to_type_flag())),
        ]);
    }

    // TODO @dkrajews: make this support printing records
    instr_vec.push(Instr::ICall("snek_print".into()));

    // Restore RBX, R12
    instr_vec.extend(vec![
        Instr::IComment("Restore RBX, R12 after main fn body".into()),
        Instr::IMov(
            Val::Reg(Reg::RBX),
            Val::RegOffset(Reg::RBP, old_rbx_rbp_offset),
        ),
        Instr::IMov(
            Val::Reg(Reg::R12),
            Val::RegOffset(Reg::RBP, old_r12_rbp_offset),
        ),
    ]);

    instr_vec.extend(FUNCTION_EPILOGUE);

    ret
}

/// Write the assembly code for a record's reference count decrement function, which decrements the reference count
/// and if the reference count hits 0, frees the memory of the record and decrements the reference count of any
/// record pointers/fields in the record
fn compile_heap_rc_decr_function_to_instrs(e: &dyn HeapAllocated, instr_vec: &mut Vec<Instr>) {
    instr_vec.push(Instr::IEnter(16));
    let record_addr_offset = push_reg_to_stack(instr_vec, 0, Reg::RDI);

    // Perform null check on the record pointer
    instr_vec.extend(vec![
        Instr::ICmp(Val::Reg(Reg::RDI), Val::Imm(0)),
        Instr::IJumpEqual(format!("{}_record_rc_decr_end", e.name()).into()),
    ]);

    // Decrement the refcount by 1 and check if it hits zero
    instr_vec.extend(vec![
        Instr::IComment("Decrement refcount by 1, compare to 0".to_string().into()),
        Instr::ISub(Val::RegOffset(Reg::RDI, 0), Val::Imm(1)),
        Instr::ICmp(Val::RegOffset(Reg::RDI, 0), Val::Imm(0)),
        Instr::IJumpNotEqual(format!("{}_record_rc_decr_end", e.name()).into()),
    ]);

    for (i, (field_name, field_type)) in e.field_types().iter().enumerate() {
        match field_type {
            ExprType::RecordPointer(type_name) | ExprType::ObjectPointer(type_name) => {
                instr_vec.push(Instr::IComment(format!(
                    "Decrement refcount of field {field_name}"
                ).into()));
                instr_vec.extend(vec![
                    // Load the address of the record struct into R11
                    Instr::IMov(
                        Val::Reg(Reg::R11),
                        Val::RegOffset(Reg::RBP, record_addr_offset),
                    ),
                    // Load the address of the field's pointer into RDI
                    Instr::IMov(
                        Val::Reg(Reg::RDI),
                        Val::RegOffset(
                            Reg::R11,
                            ((i as i32) + e.field_idx_start()) * SIZE_OF_DWORD,
                        ),
                    ),
                    Instr::ICall(format!("{type_name}_record_rc_decr").into()),
                ]);
            }
            _ => continue,
        }

        // if let ExprType::RecordPointer(field_record_type) = field_type {
        //     // If the field is a record pointer, we need to decrement the reference count of the field
        //     // and free the memory if the refcount is 0 recursively
        //     instr_vec.extend(vec![
        //         // Load the address of the record struct into R11
        //         Instr::IMov(
        //             Val::Reg(Reg::R11),
        //             Val::RegOffset(Reg::RBP, record_addr_offset),
        //         ),
        //         // Load the address of the field's pointer into RDI
        //         Instr::IMov(
        //             Val::Reg(Reg::RDI),
        //             Val::RegOffset(Reg::R11, i32::try_from(i + 1).unwrap() * SIZE_OF_DWORD),
        //         ),
        //         Instr::ICall(format!("{}_record_rc_decr", field_record_type)),
        //     ]);
        // }
    }

    // Free the record struct's memory
    instr_vec.extend(vec![
        Instr::IMov(
            Val::Reg(Reg::RDI),
            Val::RegOffset(Reg::RBP, record_addr_offset),
        ),
        Instr::ICall("free".into()), // Free the record struct
    ]);

    let n_bytes = e.alloc_size();

    // Subtract from curr heap size
    instr_vec.push(Instr::ISub(
        Val::RegOffset(Reg::R12, CURRENT_HEAP_SIZE_R12_OFFSET),
        Val::Imm(n_bytes),
    ));

    instr_vec.push(Instr::ITag(format!("{}_record_rc_decr_end", e.name()).into()));

    instr_vec.extend(FUNCTION_EPILOGUE);
}

fn compile_heap_print_function(e: &dyn HeapAllocated, instr_vec: &mut Vec<Instr>) {
    instr_vec.push(Instr::IEnter(0));

    // Move the address of the object/record into R13 (callee-saved)
    instr_vec.push(Instr::IMov(Val::Reg(Reg::R13), Val::Reg(Reg::RDI)));

    let type_name = e.name();
    let fields = e.field_types();
    let stringified_name_label = format_stringified_heap_name(&type_name);

    instr_vec.extend(vec![
        Instr::IMov(
            Val::Reg(Reg::RSI),
            Val::Imm(ExprType::RecordPointer("".to_string()).to_type_flag()),
        ),
        Instr::IMov(
            Val::Reg(Reg::R11),
            Val::Imm(ExprType::NullPtr.to_type_flag()),
        ),
        Instr::ICmp(Val::Reg(Reg::RDI), Val::Imm(0)),
        Instr::ICMovEqual(Val::Reg(Reg::RSI), Val::Reg(Reg::R11)),
        Instr::IMov(
            Val::Reg(Reg::RDI),
            Val::LabelPointer(stringified_name_label),
        ),
        Instr::ICall("snek_print".into()),
        Instr::IJumpEqual(format!("{}_print_end", type_name).into()),
    ]);

    instr_vec.extend(PRINT_OPEN_PARENS);

    for (i, (_, field_type)) in fields.iter().enumerate() {
        place_args_in_rdi_rsi(
            instr_vec,
            Val::RegOffset(Reg::R13, ((i as i32) + e.field_idx_start()) * SIZE_OF_DWORD),
            Val::Imm(field_type.to_type_flag()),
        );

        if field_type.is_heap_allocated() {
            let field_type_name = field_type.extract_heap_allocated_type_name();
            let stringified_name_label = format_stringified_heap_name(&field_type_name);

            instr_vec.extend(vec![
                Instr::IMov(Val::Reg(Reg::RSI), Val::Imm(field_type.to_type_flag())),
                Instr::IMov(
                    Val::Reg(Reg::R11),
                    Val::Imm(ExprType::NullPtr.to_type_flag()),
                ),
                Instr::ICmp(Val::Reg(Reg::RDI), Val::Imm(0)),
                Instr::ICMovEqual(Val::Reg(Reg::RSI), Val::Reg(Reg::R11)),
                Instr::IMov(
                    Val::Reg(Reg::RDI),
                    Val::LabelPointer(stringified_name_label),
                ),
            ]);
        }

        instr_vec.push(Instr::ICall("snek_print".into()));
    }

    instr_vec.extend(PRINT_CLOSED_PARENS);
    instr_vec.extend(PRINT_NEWLINE);

    instr_vec.push(Instr::ITag(format!("{}_print_end", type_name).into()));
    instr_vec.extend(FUNCTION_EPILOGUE);
}

fn compile_class_vtable(class: &Class, instr_vec: &mut Vec<Instr>) {
    let mut vtable_indices = vec![Instr::IDq("NULL".into()); class.vtable_indices.len()];

    for (method_name, (vtable_idx, method_owner_class)) in class.vtable_indices.iter() {
        println!(
            "VTable index for method {} in class {}: {}",
            method_name, method_owner_class, *vtable_idx
        );
        vtable_indices[*vtable_idx] =
            Instr::IDq(format_vtable_label(method_name, method_owner_class).into());
    }

    instr_vec.extend(vtable_indices);
}

/// Compile a program to a string of x86-64 assembly
pub fn compile(program: &Program) -> String {
    // Compile all functions to instruction strings
    let asm_section_extern = "extern snek_print
extern snek_error
extern malloc
extern free"
        .to_string();

    let mut asm_section_data = "
section .data
"
    .to_string();

    let mut asm_section_text: String = "
section .text
global our_code_starts_here

out_of_memory_error:
  enter 0, 0
  mov rdi, 4
  call snek_error
  leave
  ret

overflow_error:
  enter 0, 0
  mov rdi, 3
  call snek_error
  leave
  ret

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
        rbp_offset_stack: Vec::new(),
        rbx_offset_stack: Vec::new(),
    };

    let mut instr_vec: Vec<Instr> = Vec::new();

    // Generate assembly for freeing records/objects recursively
    let classes = program.classes.values().map(|c| c as &dyn HeapAllocated);
    let records = program
        .records
        .values()
        .map(|record| record as &dyn HeapAllocated);

    let heap_allocated_signatures = classes.chain(records);

    for signature in heap_allocated_signatures {
        let name = signature.name();

        // Add the stringified name to the data section
        let asm_stringified_name = format!(
            "{}{}\n",
            " ".repeat(N_SPACES_ASM_INDENTATION),
            format!("{} db \"{name}\", 0", format_stringified_heap_name(name))
        );

        asm_section_data.push_str(&asm_stringified_name);

        // Compile the print function for the record/object
        instr_vec.clear();
        compile_heap_print_function(signature, &mut instr_vec);

        let asm_print_func_string = format!(
            "
{name}_print:
{}
",
            compile_instrs_to_str(&instr_vec)
        );

        asm_section_text.push_str(&asm_print_func_string);

        // Compile the reference count decrement function for the record/object
        instr_vec.clear();
        compile_heap_rc_decr_function_to_instrs(signature, &mut instr_vec);

        let asm_func_string = format!(
            "
{name}_record_rc_decr:
{}
",
            compile_instrs_to_str(&instr_vec)
        );

        asm_section_text.push_str(&asm_func_string);
    }

    // Generate assembly for each function body
    let standalone_funcs = program.functions.values();
    let class_methods = program
        .classes
        .values()
        .map(|class| class.methods.values())
        .flatten();

    let funcs = standalone_funcs.chain(class_methods);

    for func in funcs {
        let name = func.name.clone();
        println!("Starting compilation for {name}");

        instr_vec.clear();
        let eval_return_type = compile_function_to_instrs(func, &mut instr_vec, &mut ctx, program);

        if eval_return_type != func.return_type {
            panic!(
                "Return type of function {name} does not match function body, expected: {:?} but got {:?}",
                func.return_type, eval_return_type
            );
        }

        let asm_func_string = format!(
            "
{name}:
{}
",
            compile_instrs_to_str(&instr_vec)
        );

        asm_section_text.push_str(&asm_func_string);
        println!("Finished compilation for {name}");
    }

    // Generate assembly for class VTables
    for (class_name, class) in program.classes.iter() {
        instr_vec.clear();
        compile_class_vtable(class, &mut instr_vec);

        let asm_func_string = format!(
            "
{class_name}_VTable:
{}
",
            compile_instrs_to_str(&instr_vec)
        );

        asm_section_text.push_str(&asm_func_string);
    }

    // Generate assembly for the main expression
    instr_vec.clear();
    let eval_return_type =
        compile_main_expr_to_instrs(&program.main_expr, &mut instr_vec, &mut ctx, program);
    if !matches!(eval_return_type, ExprType::Number | ExprType::Boolean) {
        panic!(
            "Main expression must evaluate to a number or boolean, got {:?}",
            eval_return_type
        );
    }

    let asm_main_string = format!(
        "
{MAIN_FN_TAG}:
{}
",
        compile_instrs_to_str(&instr_vec)
    );

    asm_section_text.push_str(&asm_main_string);

    let asm_string = format!(
        "{}\n{}\n{}",
        asm_section_extern, asm_section_data, asm_section_text
    );
    asm_string
}
