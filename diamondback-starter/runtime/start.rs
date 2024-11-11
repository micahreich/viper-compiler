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
    if errcode == 1 {
        eprintln!("an error ocurred: failed to parse input as u64");
    } else if errcode == 2 {
        eprintln!("an error ocurred: unknown type flag");
    } else if errcode == 3 {
        eprintln!("an error ocurred: overflow error");
    } else {
        eprintln!("an error ocurred: unknown error");
    }
    
    // let err_string = match errcode {
    //     1 => "failed to parse input as u64",
    //     2 => "unknown type flag",
    //     3 => "overflow error",
    //     _ => "unknown error",
    // };
    
    // eprintln!("an error ocurred: {}", err_string);
    std::process::exit(1);
}

#[export_name = "\x01snek_print"]
pub extern "C" fn snek_print(value: i64, type_kind: u64) {
    match type_kind {
        1 => if value == 0 { println!("false") } else { println!("true") }, // boolean
        0 => println!("{value}"), // integer
        _ => {println!("{}", type_kind); snek_error(2)}
    };
}

fn parse_input(input: &str) -> u64 {
    input.parse::<u64>().unwrap()
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let input = if args.len() == 2 { &args[1] } else { "0" };
    let input = parse_input(&input);

    let i: u64 = unsafe { our_code_starts_here(input) };
}
