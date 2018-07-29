# LJT OCaml

## Requirements
* OCaml (newer version)

## Usage

```sh
$ echo "(a /\ b) => (b /\ a)" | ocaml ljt.ml

==========================
stdin
((a ∧ b) ⊃ (b ∧ a))
success!

 •   ---->  ((a ∧ b) ⊃ (b ∧ a)) by ⊃R
 • (a ∧ b)  ---->  (b ∧ a) by ∧R

  • (a ∧ b)  ---->  b by ∧L
   • b, a  ---->  b by init

  • (a ∧ b)  ---->  a by ∧L
   • a, b  ---->  a by init
```


Some interesting unit tests:

```sh
$ ocaml ljt.ml test
```

## Issue

* The implementation of the formula parser is very naive and does not consider precedence and associativity.
Please add parentheses`(`, `)` to specify them!

## Acknowledgement
Standard ML implementation: https://github.com/ayberkt/sequents
