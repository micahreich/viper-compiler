use std::env;

#[link(name = "our_code")]
extern "C" {
    // The \x01 here is an undocumented feature of LLVM that ensures
    // it does not add an underscore in front of the name.
    // Courtesy of Max New (https://maxsnew.com/teaching/eecs-483-fa22/hw_adder_assignment.html)
    #[link_name = "\x01our_code_starts_here"]
    fn our_code_starts_here(input: u64, heap_size: u64) -> u64;
}

#[export_name = "\x01snek_error"]
pub extern "C" fn snek_error(errcode: i64) {
    match errcode {
        1 => eprintln!("an error ocurred: failed to parse input as u64"),
        2 => eprintln!("an error ocurred: unknown type flag"),
        3 => eprintln!("an error ocurred: overflow error"),
        4 => eprintln!("an error ocurred: out of memory"),
        _ => eprintln!("an error ocurred: unknown error"),
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
        0 => print!("\n"),
        1 => if value == 0 { print!("( ") } else { print!(")") }
        2 => print!("{value} "), // integer
        3 => if value == 0 { print!("false ") } else { print!("true") }, // boolean
        5 => print!("NULL "),
        4 => {
            // Treat `value` as a pointer to a null-terminated string
            let c_string = unsafe { std::ffi::CStr::from_ptr(value as *const i8) };
            if let Ok(rust_string) = c_string.to_str() {
                print!("{rust_string} ");
            } else {
                print!("<invalid string>");
            }
        }
        _ => snek_error(2),
    };
}

fn parse_input(input: &str) -> u64 {
    input.parse::<u64>().unwrap()
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let input = if args.len() >= 2 { &args[1] } else { "0" };
    let heap_size = if args.len() == 3 { &args[2] } else { "10000" };
    let input = parse_input(&input);
    let heap_size = parse_input(&heap_size);

    let i: u64 = unsafe { our_code_starts_here(input, heap_size) };
}
