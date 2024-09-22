mod infra;

// Your tests go here!
success_tests! {
    {
        name: false_val,
        file: "false_val.snek",
        expected: "false",
    },
    {
        name: example1,
        file: "example1.snek",
        expected: "6",
    },
    {
        name: example2,
        file: "example2.snek",
        expected: "-6",
    },
    {
        name: factorial0,
        file: "factorial.snek",
        input: "0",
        expected: "1",
    },
    {
        name: factorial1,
        file: "factorial.snek",
        input: "1",
        expected: "1",
    },
    {
        name: factorial2,
        file: "factorial.snek",
        input: "2",
        expected: "2",
    },
    {
        name: factorial3,
        file: "factorial.snek",
        input: "3",
        expected: "6",
    },
    {
        name: input_compare_1,
        file: "input_compare.snek",
        input: "2",
        expected: "false",
    },
    {
        name: input_compare_2,
        file: "input_compare.snek",
        input: "10",
        expected: "true",
    },
}

runtime_error_tests! {
    {
        name: mul_over,
        file: "mul_over.snek",
        expected: "overflow",
    },
}

static_error_tests! {
    {
        name: invalid_argument,
        file: "invalid_argument.snek",
        expected: "mismatch",
    },
    {
        name: number_bounds_fail,
        file: "number_bounds_fail.snek",
        expected: "Invalid",
    },
    {
        name: unbound,
        file: "unbound.snek",
        expected: "Unbound"
    },
    {
        name: duplicate,
        file: "duplicate_binding.snek",
        expected: "Duplicate"
    },
    {
        name: reserved,
        file: "reserved.snek",
        expected: "keyword"
    },
    {
        name: reserved_bool,
        file: "reserved_bool.snek",
        expected: "keyword"
    }
}
