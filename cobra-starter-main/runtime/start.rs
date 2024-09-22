use std::env;

#[link(name = "our_code")]
extern "C" {
    // The \x01 here is an undocumented feature of LLVM that ensures
    // it does not add an underscore in front of the name.
    // Courtesy of Max New (https://maxsnew.com/teaching/eecs-483-fa22/hw_adder_assignment.html)
    #[link_name = "\x01our_code_starts_here"]
    fn our_code_starts_here(input: u64) -> u64;
}

#[export_name = "\x01snek_error"]
pub extern "C" fn snek_error(errcode: i64) {
    let err_string = match errcode {
        1 => "Failed to parse input as u64",
        2 => "Unknown type flag",
        _ => "Unknown error",
    };
    
    eprintln!("an error ocurred: {}", err_string);
    std::process::exit(1);
}

#[export_name = "\x01snek_print"]
pub extern "C" fn snek_print(value: i64, type_flag: u64) {
    match type_flag {
        1 => if value == 0 { println!("false") } else { println!("true") }, // boolean
        0 => println!("{value}"), // integer
        _ => snek_error(2),
    };
}


fn parse_input(input: &str) -> u64 {
    input.parse::<u64>().unwrap()
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let input = if args.len() == 2 { &args[1] } else { "0" };
    let input = parse_input(&input);

    let _ = unsafe { our_code_starts_here(input) };
}
