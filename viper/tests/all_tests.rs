mod infra;

// Your tests go here!
success_tests! {
    {
        name: fact,
        file: "fact.snek",
        input: "10",
        expected: "3628800",
    },
    {
        name: even_odd_1,
        file: "even_odd.snek",
        input: "10",
        expected: "10\ntrue\ntrue",
    },
    {
        name: even_odd_2,
        file: "even_odd.snek",
        input: "9",
        expected: "9\nfalse\nfalse",
    },
    {
        name: num,
        file: "num.snek",
        expected: "644",
    },
    {
        name: add1_sub1,
        file: "add1_sub1.snek",
        expected: "4",
    },
    {
        name: nested_arith0,
        file: "nested_arith0.snek",
        expected: "35",
    },
    {
        name: nested_arith1,
        file: "nested_arith1.snek",
        expected: "25",
    },
    {
        name: nested_arith2,
        file: "nested_arith2.snek",
        expected: "0",
    },
    {
        name: nested_arith3,
        file: "nested_arith3.snek",
        expected: "1117",
    },
    {
        name: nested_arith4,
        file: "nested_arith4.snek",
        expected: "-1",
    },
    {
        name: binding0,
        file: "binding0.snek",
        expected: "5",
    },
    {
        name: binding1,
        file: "binding1.snek",
        expected: "-5",
    },
    {
        name: binding_expr,
        file: "binding_expr.snek",
        expected: "1225",
    },
    {
        name: binding_nested,
        file: "binding_nested.snek",
        expected: "1",
    },
    {
        name: complex_expr,
        file: "complex_expr.snek",
        expected: "6",
    },
    {
        name: quick_brown_fox,
        file: "quick_brown_fox.snek",
        expected: "-3776",
    },
    {
        name: binding_chain,
        file: "binding_chain.snek",
        expected: "3",
    },
    {
        name: binding_nested_chain,
        file: "binding_nested_chain.snek",
        expected: "12",
    },
    {
        name: shadowed_binding_succ0,
        file: "shadowed_binding_succ0.snek",
        expected: "100",
    },
    {
        name: shadowed_binding_succ1,
        file: "shadowed_binding_succ1.snek",
        expected: "7",
    },
    {
        name: shadowed_binding_succ2,
        file: "shadowed_binding_succ2.snek",
        expected: "150",
    },
    {
        name: shadowed_binding_succ3,
        file: "shadowed_binding_succ3.snek",
        expected: "5",
    },
    {
        name: shadowed_binding_succ4,
        file: "shadowed_binding_succ4.snek",
        expected: "18",
    },
    {
        name: shadowed_binding_succ5u,
        file: "shadowed_binding_succ5.snek",
        expected: "5",
    },
    {
        name: shadowed_binding_succ6,
        file: "shadowed_binding_succ6.snek",
        expected: "3",
    },
}

runtime_error_tests! {}

static_error_tests! {
    {
        name: duplicate_params,
        file: "duplicate_params.snek",
        expected: "",
    },
    {
        name: parse_sexp_fail1,
        file: "parse_sexp_fail1.snek",
        expected: "Invalid",
    },
    {
        name: parse_sexp_fail2,
        file: "parse_sexp_fail2.snek",
        expected: "Invalid",
    },
    {
        name: parse_token_fail1,
        file: "parse_token_fail1.snek",
        expected: "Invalid",
    },
    {
        name: parse_token_fail2,
        file: "parse_token_fail2.snek",
        expected: "Invalid",
    },
    {
        name: parse_token_fail3,
        file: "parse_token_fail3.snek",
        expected: "Invalid",
    },
    {
        name: parse_token_fail4,
        file: "parse_token_fail4.snek",
        expected: "Invalid",
    },
    {
        name: parse_op_fail1,
        file: "parse_op_fail1.snek",
        expected: "Invalid",
    },
    {
        name: parse_op_fail2,
        file: "parse_op_fail2.snek",
        expected: "Invalid",
    },
    {
        name: parse_op_fail3,
        file: "parse_op_fail3.snek",
        expected: "Invalid",
    },
    {
        name: parse_op_fail4,
        file: "parse_op_fail4.snek",
        expected: "Invalid",
    },
    {
        name: parse_op_fail5,
        file: "parse_op_fail5.snek",
        expected: "Invalid",
    },
    {
        name: parse_let_nobindings_fail,
        file: "parse_let_nobindings_fail.snek",
        expected: "Invalid",
    },
    {
        name: parse_let_improperargs_fail1,
        file: "parse_let_improperargs_fail1.snek",
        expected: "Invalid",
    },
    {
        name: parse_let_improperargs_fail2,
        file: "parse_let_improperargs_fail2.snek",
        expected: "Invalid",
    },
    {
        name: parse_let_improperargs_fail3,
        file: "parse_let_improperargs_fail3.snek",
        expected: "Invalid",
    },
    {
        name: parse_let_improperargs_fail4,
        file: "parse_let_improperargs_fail4.snek",
        expected: "Invalid",
    },
    {
        name: parse_let_improperargs_fail5,
        file: "parse_let_improperargs_fail5.snek",
        expected: "Invalid",
    },
    {
        name: unbound_identifier_fail0,
        file: "unbound_identifier_fail0.snek",
        expected: "Unbound variable identifier x",
    },
    {
        name: unbound_identifier_fail1,
        file: "unbound_identifier_fail1.snek",
        expected: "Unbound variable identifier y",
    },
    {
        name: unbound_identifier_fail2,
        file: "unbound_identifier_fail2.snek",
        expected: "Unbound variable identifier x",
    },
    {
        name: duplicate_binding_fail0,
        file: "duplicate_binding_fail0.snek",
        expected: "Duplicate binding",
    },
    {
        name: duplicate_binding_fail1,
        file: "duplicate_binding_fail1.snek",
        expected: "Duplicate binding",
    },
    {
        name: duplicate_binding_fail2,
        file: "duplicate_binding_fail2.snek",
        expected: "Duplicate binding",
    },
}
