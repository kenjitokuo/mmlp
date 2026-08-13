# MMLP

MMLP is an OCaml implementation of multimodal logic programming with full formulas.

Programs and queries may be arbitrary first-order multimodal formulas. They are not restricted to Horn clauses or to separate program and goal grammars. Boolean connectives, quantifiers, and indexed modal operators may occur at arbitrary depth.

MMLP performs symbolic proof search, computes substitutions for selected query variables, and checks the resulting proof derivations before returning answers.

## Features

- Full first-order formulas as programs and queries
- Multiple indexed modal operators
- Modal principles D, T, I, B, 4, and 5
- Nested proof search with finite grammar certificates
- Scoped unification for quantified proof search
- Computed answer substitutions
- Focused proof search
- Proof checking

## Build

MMLP requires OCaml and Dune.

Build the project with:

```sh
dune build
```

Run the test suite with:

```sh
dune runtest
```

## Command-line usage

The executable is `mmlp`.

```text
mmlp --query FORMULA
     [--program FORMULA ...]
     [--answer VARIABLE ...]
     [--axiom AXIOM ...]
     [--depth N]
     [--max-modal-index N]
```

When running directly from the source tree, use:

```sh
dune exec mmlp -- --query "FORMULA"
```

A query is required. Program formulas, answer variables, and modal axioms are supplied with repeatable options.

### `--program FORMULA`

Adds a formula to the program.

The option may be repeated:

```sh
dune exec mmlp -- \
  --program "p -> q" \
  --program "p" \
  --query "q"
```

Free variables occurring in program formulas are implicitly universally closed.

For example:

```sh
dune exec mmlp -- --program "p(X)" --query "p(c)"
```

treats the free variable in the program formula universally.

### `--query FORMULA`

Specifies the query.

Queries are not restricted to atomic goals. For example:

```sh
dune exec mmlp -- --program "p" --query "p or q"
```

is a valid query.

### `--answer VARIABLE`

Selects a free variable of the query whose computed value should be returned.

For example:

```sh
dune exec mmlp -- \
  --program "p(c)" \
  --query "p(X)" \
  --answer X
```

asks MMLP to compute an answer for `X`.

More than one answer variable may be selected by repeating `--answer`.

### `--axiom AXIOM`

Adds an instance of a modal principle.

Supported forms are:

```text
D:i
T:i
I:i,j
B:i,j
4:i,j,k
5:i,j,k
```

For example:

```sh
dune exec mmlp -- \
  --program "box[1] p" \
  --query "p" \
  --axiom "T:1"
```

uses modal principle T for modality 1.

Several modal principles may be combined by repeating `--axiom`.

### `--depth N`

Sets the proof-search depth bound.

A larger value allows deeper proofs to be explored, at the cost of additional search.

### `--max-modal-index N`

Sets the largest modal index accepted in formulas and modal axiom specifications.

For example, formulas using `box[2]` or `diamond[2]` require a maximum modal index of at least 2.

## Formula syntax

Typical formulas include:

```text
p
p(X)
p(f(X),c)

not p
p and q
p or q
p -> q

forall x. p(x)
exists x. p(x)

box[1] p
diamond[1] p
```

The connectives may be nested freely. For example:

```text
forall x. (box[1] p(x) -> diamond[2] q(x))
```

is a valid source formula when the modal index bound permits modalities 1 and 2.

The parser also accepts the following ASCII alternatives:

```text
~A
!A
A & B
A | B
```

## Examples

### First-order computed answer

```sh
dune exec mmlp -- \
  --program "p(c)" \
  --query "p(X)" \
  --answer X \
  --depth 4
```

### Program with implication

```sh
dune exec mmlp -- \
  --program "p -> q" \
  --program "p" \
  --query "q" \
  --depth 6
```

### Quantified program

```sh
dune exec mmlp -- \
  --program "forall x. (p(x) -> q(x))" \
  --program "p(c)" \
  --query "q(c)" \
  --depth 8
```

### Modal reasoning with T

```sh
dune exec mmlp -- \
  --program "box[1] p" \
  --query "p" \
  --axiom "T:1" \
  --depth 4
```

### Multiple modalities

```sh
dune exec mmlp -- \
  --program "box[2] p" \
  --query "box[1] p" \
  --axiom "I:1,2" \
  --max-modal-index 2 \
  --depth 6
```

## Repository layout

```text
bin/    command-line interface
lib/    implementation
test/   tests
```

## Author

Kenji Tokuo
