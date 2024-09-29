use std::env;
use std::fs::File;
use std::io::prelude::*;
use sexp::*;

mod types;
mod parsing;
mod compilation;

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();

    let in_name = &args[1];
    let out_name = &args[2];

    let mut in_file = File::open(in_name)?;
    let mut in_contents = String::new();
    in_file.read_to_string(&mut in_contents)?;

    // You will make result hold the result of actually compiling
    let parsing_result = parsing::parse_expr(&parse(&in_contents).unwrap());
    let compilation_result = compilation::compile(&parsing_result);

    let asm_program = format!(
        "
extern snek_print
extern snek_error

section .text
global our_code_starts_here

overflow_error:
  mov rdi, 3
  call snek_error

our_code_starts_here:
{}
  ret
",
    compilation_result
    );

    let mut out_file = File::create(out_name)?;
    out_file.write_all(asm_program.as_bytes())?;

    Ok(())
}

