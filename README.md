<!-- Logo and Title Section -->
<h1 align="center">🐍  Viper: Language & Compiler</h1>

<div align="center">
  <a href="#"><img src="https://img.shields.io/badge/Rust-%23000000.svg?e&logo=rust&logoColor=white" alt="Rust"></a>
  <img src="https://img.shields.io/badge/License-MIT-green.svg" alt="MIT License">
</div>

## Introduction

Viper is a simple programming language modeled after Lisp and ML. The language and compiler were written as an educational exercise to learn about programming language and compiler design. The compiler is written in Rust and designed to produce machine code for x86-64 Linux systems. 

## Features 

Viper has many standard programming language features, including:
- Arithmetic functionality
- Variable binding
- Scoping / shadowing
- Functions
- Heap-allocated structs / records
- Classes and objects with dynamic dispatch
- Garbage collection
- Command-line input

## Example Code

A Viper "hello world" program declares and adds two variables;
```lisp
(let
    ((x 1) (y 2)) ;; declare variables x, y in a let block
    (+ x y)       ;; add them together and return the result
)
```

Below you can find examples which are meant to demonstrate specific language features.

### Binary Search Tree

The following Viper program declares a BST record and writes some functions to build an initial tree, insert values, and search the tree, with nodes allocated on the heap and garbage collected in the end:

```lisp
;; declare the BST node record
(record bst_node ((val int) (left bst_node) (right bst_node)))

;; write the insert function to insert a value in the BST
(fun insert_value ((val int) (root bst_node)) bst_node
    (if
        (= root NULL)
        (bst_node val NULL NULL)
        (let
            ((curr_val (lookup root val)))
            (block
                (if
                    (< val curr_val)
                    (set! root left (insert_value val (lookup root left)))
                    (if
                        (= val curr_val)
                        root
                        (set! root right (insert_value val (lookup root right)))
                    )
                )
                root
            )
        )
    )
)

;; write the search function to check if a value is in the BST
(fun search_value ((val int) (root bst_node)) bool
    (if
        (= root NULL) 
        false
        (let
            ((curr_val (lookup root val)))
            (if 
                (= curr_val val)
                true
                (if (< val curr_val)
                    (search_value val (lookup root left))
                    (search_value val (lookup root right))
                )
            )
        )
    )
)

;; the main expression builds a sample BST and inserts the user input
(let
    ((root (bst_node 10 (bst_node 3 NULL NULL) (bst_node 20 NULL NULL))))
    (block 
        ;; should return T/F depending on if the user input is in the tree already
        (print (search_value input root))
        (set! root (insert_value input root))
        ;; should always return T since we just inserted it
        (print (search_value input root))
    )
)
```

### Collections via OOP

TODO

## Limitations and Future Work

Viper is not fully feature-complete, with the following as notable points for future work and improvement:
- Comments
- Peephole optimization via register allocation, constant folding, constant propagation
- Cycle-detection in the reference counter-based GC system
- Redundant load/stores, instruction optimization
- Cross-platform compilation / support for ARM processors