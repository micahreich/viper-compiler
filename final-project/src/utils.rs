use regex::Regex;
use crate::types::*;

/// Place values into 1st ($rdi) and 2nd ($rsi) arguments for a function call
pub fn place_args_in_rdi_rsi(ctx: &mut CompileCtx, rdi: Val, rsi: Val) {
    ctx.instr_vec.extend([
        Instr::IMov(Val::Reg(Reg::RDI), rdi),
        Instr::IMov(Val::Reg(Reg::RSI), rsi),
    ]);
}

/// Determine if a string is a valid identifier; must not be a reserved keyword, must not be a number
pub fn is_valid_identifier(s: &str) -> bool {
    if RESERVED_KEYWORDS.into_iter().any(|k| k == s) {
        return false;
    }

    let number_regex = Regex::new(r"^\d+(\.\d+)?$").unwrap();
    if number_regex.is_match(s) {
        return false;
    }

    true
}

/// Format the name of a record or object as what label it will appear as in the .data section when
/// writing out the const string representing the heap-allocated type's name
pub fn format_stringified_heap_name_label(name: &String) -> String {
    format!("__{name}_heapobj_string")
}

/// Format the name of an object's method as what label it will appear as in the .text section when
/// writing out the method body assembly
pub fn format_method_name_label(class_name: &String, method_name: &str) -> String {
    format!("__{}_{}", class_name, method_name)
}

/// Round a positive integer up to the next multiple of 16
pub fn round_up_to_next_multiple_of_16(n: i32) -> i32 {
    (n + 15) & !15
}
