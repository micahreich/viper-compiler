mod infra;

// Your tests go here!
success_tests! {
    add1: "73",
    add: "15",
    nested_arith: "25",
    binding: "5",
    custom1: "5",
    custom2: "5",
    custom3: "8",
    custom4: "7",
    custom5: "18",
    custom7: "13",
    custom9: "5",
}

failure_tests! {
    unbound_id: "Unbound variable identifier x",
    duplicate_binding: "Duplicate binding",
    custom6: "Invalid program: malformed expression",
    custom8: "Invalid program: malformed expression",
}
