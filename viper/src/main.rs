use sexp::*;
use std::env;
use std::fs::File;
use std::io::prelude::*;

mod compilation;
mod parsing;
mod types;
mod utils;
use std::time::Instant;

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();

    let in_name = &args[1];
    let out_name = &args[2];

    let start = Instant::now();

    let mut in_file = File::open(in_name)?;
    let mut in_contents = String::new();
    in_file.read_to_string(&mut in_contents)?;

    in_contents.insert(0, '(');
    in_contents.insert(in_contents.len(), ')');

    let parsed_contents = match parse(&in_contents) {
        Ok(contents) => contents,
        Err(_) => panic!("Invalid: failed to parse sexp"),
    };

    let parsed_program = parsing::parse_prog(&parsed_contents);
    let compilation_result = compilation::compile(&parsed_program);

    let duration = start.elapsed();
    println!("Compilation of {} complete, took {:.2}s", in_name, duration.as_secs_f32());

    let mut out_file = File::create(out_name)?;
    out_file.write_all(compilation_result.as_bytes())?;

    Ok(())
}
