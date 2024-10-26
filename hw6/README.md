# HW6: Static semantics

- authors:
  - Jonathan Aldrich <https://www.cs.cmu.edu/~aldrich/>
  - Sam Estep <https://samestep.com/>

Due Wednesday, October 23, 11:59pm

In this sixth homework assignment, you'll extend the simply typed lambda
calculus with `if`/`then`/`else` and `rec` (similar to the modeling you did in
HW3), and then repair progress and preservation proofs to show soundness of
those extensions.

## Assignment structure

The structure of the files in this assignment mirrors that of HW3.

## Exercises

In code comments, `slf/edu/cmu/cs/plp/hw6.slf` file also contains instructions
similar to the ones below.

### Model `if`/`then`/`else`

Add these two cases to the syntax for expressions (you may also need to modify
the set of `terminals`):

    | ?b
    | if e then e else e

You already wrote small-step semantics for these in HW3. Copy those into here,
making the necessary changes to correct any feedback you got on your HW3
submission. If you're not sure exactly what these dynamic semantics should be,
please refer to Piazza.

Next, add this case to the syntax for types:

    | bool

Then, extend the `value` and `has-type` judgments to account for these new
syntactic cases you've added.

### Model `rec`

Add this case to the language syntax (again, you may also need to modify the set
of `terminals`):

    | rec x : tau = e[x]

You already wrote small-step semantics for this in HW3. Copy that into here,
making the necessary changes to correct any feedback you got on your HW3
submission. You'll also need to account for the fact that `x` now has a type
annotation, which it didn't have in HW3. If you're not sure exactly what these
dynamic semantics should be, please refer to Piazza.

Then, extend the `has-type` judgment to account for this new syntactic case
you've added.

### Repair the proof of `progress`

After finishing your modeling, you should see errors in the proof of the
`progress` theorem. Fix those errors to complete the proof. While doing this,
you may realize that the static semantics you wrote aren't quite right. That's
ok! Fix them and then come back to the proof.

### Repair the proof of `preservation`

Now do the same thing for the proof of the `preservation` theorem.

## Submit

On Gradescope, simply submit your `hw6.slf` file.

# Rubric

| total                                  | 100% |
|----------------------------------------|-----:|
| correct modeling of `if`/`then`/`else` |  15% |
| correct modeling of `rec`              |  15% |
| correct proof of `progress`            |  30% |
| correct proof of `preservation`        |  30% |
| code style                             |  10% |
