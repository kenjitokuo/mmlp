type equation =
  Symbolic_term.term * Symbolic_term.term

type result =
  | Solved of Symbolic_substitution.t * Symbolic_term.supply
  | Unsolvable

val solve :
  supply:Symbolic_term.supply ->
  equation list ->
  result
