use core::panic;
use std::collections::HashSet;

use crate::types::*;

fn push_rax_to_stack(instr_vec: &mut Vec<Instr>, rsp_offset: i32) -> i32 {
    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RSP, rsp_offset + SIZE_OF_NUMBER),
        Val::Reg(Reg::RAX),
    ));
    rsp_offset + SIZE_OF_NUMBER
}

fn compile_to_instrs(
    e: &Expr,
    scope: &mut VariableScope,
    instr_vec: &mut Vec<Instr>,
    rsp_offset: &mut i32,
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
        Expr::Id(s) => {
            if s == "input" {
                instr_vec.push(Instr::IMov(
                    Val::Reg(Reg::RAX),
                    Val::RegOffset(Reg::RSP, SIZE_OF_NUMBER),
                ));

                ExprType::Number
            } else {
                match scope.get(s) {
                    Some((s_rsp_offset, e_type)) => {
                        instr_vec.push(Instr::IMov(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, *s_rsp_offset),
                        ));

                        *e_type
                    }
                    None => panic!("Unbound variable identifier {s}"),
                }
            }
        }
        Expr::UnOp(op, e) => {
            let e_type = compile_to_instrs(e, scope, instr_vec, rsp_offset, tag_id);

            if e_type != ExprType::Number {
                panic!("Invalid type for unary operation");
            }

            match op {
                Op1::Add1 => instr_vec.push(Instr::IAdd(Val::Reg(Reg::RAX), Val::Imm(1))),
                Op1::Sub1 => instr_vec.push(Instr::ISub(Val::Reg(Reg::RAX), Val::Imm(1))),
            };

            instr_vec.push(Instr::IJumpOverflow("overflow_error".to_string()));

            ExprType::Number
        }
        Expr::BinOp(op, e1, e2) => {
            // Compile e2 first so that subtraction works nicely, leaves e1 in rax
            let e2_type = compile_to_instrs(e2, scope, instr_vec, rsp_offset, tag_id);
            let rsp_offset_e2_eval = push_rax_to_stack(instr_vec, *rsp_offset);
            *rsp_offset = rsp_offset_e2_eval;

            let e1_type = compile_to_instrs(e1, scope, instr_vec, rsp_offset, tag_id); // e1 is in rax

            // Perform some type checking on the arguments
            if *op == Op2::Equal && e1_type != e2_type {
                panic!("Type mismatch in equality comparison");
            } else if e1_type != ExprType::Number || e2_type != ExprType::Number {
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
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));

                        instr_vec.push(Instr::ICMovEqual(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::Less => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));

                        instr_vec.push(Instr::ICMovLess(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::LessEqual => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
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
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::RAX), Val::Imm(0)));

                        instr_vec.push(Instr::IMov(Val::Reg(Reg::R10), Val::Imm(1)));

                        instr_vec.push(Instr::ICMovGreater(Val::Reg(Reg::RAX), Val::Reg(Reg::R10)));
                    }
                    Op2::GreaterEqual => {
                        instr_vec.push(Instr::ICmp(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
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
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));
                    }
                    Op2::Minus => {
                        instr_vec.push(Instr::ISub(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));
                    }
                    Op2::Times => {
                        instr_vec.push(Instr::IMul(
                            Val::Reg(Reg::RAX),
                            Val::RegOffset(Reg::RSP, rsp_offset_e2_eval),
                        ));
                    }
                    _ => unreachable!(),
                }

                instr_vec.push(Instr::IJumpOverflow("overflow_error".to_string()));
                return ExprType::Number;
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
                    panic!("Reserved keyword used as variable name in let expression");
                }

                let var_e_type = compile_to_instrs(var_e, scope, instr_vec, rsp_offset, tag_id);
                *rsp_offset = push_rax_to_stack(instr_vec, *rsp_offset);

                if existing_identifiers.contains(var) {
                    panic!("Duplicate binding");
                } else {
                    existing_identifiers.insert(var.clone());
                    scope.insert(var.clone(), (*rsp_offset, var_e_type));
                }
            }

            // Compile the expression
            let e_type = compile_to_instrs(e, scope, instr_vec, rsp_offset, tag_id);

            // Restore original scope after the let expression is finished
            *scope = original_scope;

            e_type
        }
        Expr::Set(id, e1) => {
            let e1_type = compile_to_instrs(e1, scope, instr_vec, rsp_offset, tag_id);
            let (id_offset, _) = scope.get(id).unwrap();

            instr_vec.push(Instr::IMov(
                Val::RegOffset(Reg::RSP, *id_offset),
                Val::Reg(Reg::RAX),
            ));
            // scope.insert(id.clone(), (*rsp_offset, e1_type)); // Update the stack offset for variable 'id'

            e1_type
        }
        Expr::Block(expr_vec) => {
            let mut last_e_type = ExprType::Number;

            for e in expr_vec {
                last_e_type = compile_to_instrs(e, scope, instr_vec, rsp_offset, tag_id);
            }

            last_e_type
        }
        Expr::If(e1, e2, e3) => {
            let curr_tag_id = *tag_id;

            *tag_id += 1;
            // Compile e1
            compile_to_instrs(e1, scope, instr_vec, rsp_offset, tag_id);

            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            // If e1 evaluates to false, go to e3
            instr_vec.push(Instr::IJumpEqual(format!("else{curr_tag_id}")));

            // Compile e2
            let return_type = compile_to_instrs(e2, scope, instr_vec, rsp_offset, tag_id);
            instr_vec.push(Instr::IJump(format!("end{curr_tag_id}")));

            // Compile e3
            instr_vec.push(Instr::ITag(format!("else{curr_tag_id}")));

            compile_to_instrs(e3, scope, instr_vec, rsp_offset, tag_id);

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
            let return_type = compile_to_instrs(e1, scope, instr_vec, rsp_offset, tag_id);
            let rsp_offset_return = push_rax_to_stack(instr_vec, *rsp_offset);
            *rsp_offset = rsp_offset_return;

            // Compile e2
            compile_to_instrs(e2, scope, instr_vec, rsp_offset, tag_id);
            // If e2 returned false, keep going
            instr_vec.push(Instr::ICmp(Val::Reg(Reg::RAX), Val::Imm(0)));
            instr_vec.push(Instr::IJumpEqual(format!("loop{curr_tag_id}")));

            instr_vec.push(Instr::IMov(
                Val::Reg(Reg::RAX),
                Val::RegOffset(Reg::RSP, rsp_offset_return),
            ));

            instr_vec.push(Instr::ITag(format!("end{curr_tag_id}")));

            return_type
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
        Instr::IMov(dst, src) => format!("mov {}, {}", val_to_str(dst), val_to_str(src)),
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
    }
}

fn reg_to_str(r: &Reg) -> String {
    match r {
        Reg::RAX => "rax".to_string(),
        Reg::RSP => "rsp".to_string(),
        Reg::RDI => "rdi".to_string(),
        Reg::RSI => "rsi".to_string(),
        Reg::R10 => "r10".to_string(),
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
                format!("[{}-{v}]", reg_to_str(r), v = i)
            }
        }
    }
}

pub fn compile(e: &Expr) -> String {
    let scope = &mut VariableScope::new();
    let mut instr_vec: Vec<Instr> = Vec::new();
    let mut rsp_offset = SIZE_OF_NUMBER;
    let mut tag_id = 0;

    // instr_vec.push(Instr::ISub((Val::Reg(Reg::RSP)), (Val::Imm(8))));

    // Push the input value to the stack
    instr_vec.push(Instr::IMov(
        Val::RegOffset(Reg::RSP, SIZE_OF_NUMBER),
        Val::Reg(Reg::RDI),
    ));

    let return_type = compile_to_instrs(e, scope, &mut instr_vec, &mut rsp_offset, &mut tag_id);

    // Call print function with final result
    instr_vec.push(Instr::IMov(Val::Reg(Reg::RDI), Val::Reg(Reg::RAX)));
    instr_vec.push(Instr::IMov(
        Val::Reg(Reg::RSI),
        Val::Imm(return_type.to_type_flag()),
    ));
    instr_vec.push(Instr::ICall("snek_print".to_string()));

    // Turn the instructions into a multi-line string
    compile_instrs_to_str(&instr_vec)
}
