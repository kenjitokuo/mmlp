type word = Modal_symbol.t list

type production = {
  lhs : word;
  rhs : word;
}

val converse_production : production -> production

val base_production_of_axiom :
  Modal_axiom.t -> production option

val compare_word : word -> word -> int

val compare_production : production -> production -> int

module Production_set : Stdlib.Set.S with type elt = production

val of_axioms :
  Modal_axiom.Set.t -> Production_set.t
