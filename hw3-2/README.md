# HW3: Dynamic Semantics

- author: Sam Estep <https://samestep.com/>
- author: Jonathan Aldrich

Due Friday, September 20, 11:59pm

In this third homework assignment, you'll do a couple things:

- prove half of the fact that big-step and small-step semantics (for a small
  language) are equivalent
- model a couple additional constructs in that language (without proving
  properties about those new constructs, other than using them for simple
  derivations)

## Assignment structure

The structure of the files in this assignment mirrors that of Recitation 3.

## Exercises

### Prove `big-implies-small`

As mentioned in a comment in the code, you'll probably need to define and prove
some helper lemmas in order to finish this proof.

After you finish this step, SASyLF should give you no errors or warnings.

### Model `if`/`then`/`else`

Add a syntactic case for boolean literals to the language (we're using `?` as a
prefix just like we use `#` as a prefix for natural number literals):

    ?b

Also add a syntactic case `if` expressions:

    if e then e else e

Informally, its semantics are: If the condition evaluates to `T`, take the first
branch. If the condition evaluates to `F`, take the second branch.  Your
semantics should only evaluate the branch of the if that corresponds to the
condition, not both branches.

Add rule(s) to the `value`, `eval`, and `reduce` judgments as necessary to model
these new syntactic and semantic rules.

Hints: remember that small-step semantics should include congruence rules where
appropriate.  Also remember to keep small-step and big-step semantics separate;
they should not use one another.

After you finish this step, all the errors/warnings SASyLF gives you should be
in the proofs, _not_ in your definitions of syntax or semantics. For this
homework assignment, you do not need to repair the proofs to account for this
new language construct.

### Model `rec`

Add this syntactic case to the language:

    rec x = e[x]

Recall that `e[x]` means an expression called `e` which binds `x`. Informally,
its semantics are that this expression is equivalent to the expression `e`
itself with `x` replaced by the whole expression `rec x = e[x]`. (You could
imagine using this construct to define recursive functions.)

Add rule(s) to the `eval` and `reduce` judgments to model these semantics.

#### `rec` Example
A simple `rec` example would be implementing the Fibonacci sequence using our earlier definition of `if` (assume we also define equality rules that evaluate to booleans, which isn't required for this assignment).


```
rec fib = fn x {
  if x = 0 then 1 else
  if x = 1 then 1 else
  fib (x - 2) + fib (x - 1)
}
```
Imagine calling `fib` with the argument `2`. The evaluation goes like this:
```
(rec fib = fn x { ... }) 2 ->
  fn x {
    if x = 0 then 1 else
    if x = 1 then 1 else
    (rec fib = fn x { ... }) (x - 2) + (rec fib = fn x { ... }) (x - 1) 
  } 2
```

After you finish this step, all the errors/warnings SASyLF gives you should be
in the proofs, not in your definitions of syntax or semantics. For this homework
assignment, you do not need to repair the proofs to account for this new
language construct.

#### `rec` test cases

Uncomment theorems `rec-test1` and `rec-test2` and prove them.  These theorems
test your semantics for `rec` and can help make sure you are on the right track.
There are still things that can go wrong, however, so consider proving more
test theorems and follow the homework specification carefully.

## Modeling Advice

Here's some advice on modeling language constructs, which may help with the
tasks above.

 * Big step semantics should evaluate an expression all the way to a value.  For example, the following rule for function call is **incorrect** because it does not evaluate the body of a function after substituting the argument into the body:

e1 => fn x { e[x] }
e2 => e2'
------------------- eval-call
e1 e2 => e[e2']

 * Small step semantics should not use big-step semantics to evaluate parts to a value, because that would mean taking more than one small step.  Instead, congruence rules should be used.  For example, the following small-step rule for function call is **incorrect** because it uses big step semantics to evaluate the argument expression to a value:

e2 => e2'
--------------------------- r-call  
(fn x { e[x] }) e2 -> e[e2']

 * Small step semantics should never do more than one thing.  For example, the following small-step rule for function call is **incorrect** because it both (A) substitutes the argument into the body of the function and (B) then has the function body take a step:

e2 value
e[e2] -> e'  
--------------------------- r-call
(fn x { e[x] }) e2 -> e'

*   Small step semantics should be careful not to force something to take a step when it might be a value.  Another problem with the rule above is that `e[e2]` might be a value (e.g. if `e[x]` was already a value such as `true`) in which case the rule cannot be applied at all!

## Submit

Comment out the `eval` rules you added along with `rec-test1` and `rec-test2`,
so that SASyLF again gives no errors/warnings. Then, on Gradescope, simply
submit your `hw3.slf` file for the HW3 assignment.

# Rubric

| total                                  | 100% |
|----------------------------------------|-----:|
| correct proof of `big-implies-small`   |  45% |
| correct modeling of `if`/`then`/`else` |  20% |
| correct modeling of `rec`              |  20% |
| proving rec-test1/rec-test2            |  05% |
| code style                             |  10% |
