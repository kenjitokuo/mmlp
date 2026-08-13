type formula_occurrence = {
  occurrence_id : Nested_sequent.occurrence_id;
  position : Nested_sequent.position;
  formula : Symbolic_formula.t;
}

type t

val tree :
  t ->
  Nested_sequent.t

val formulas :
  t ->
  formula_occurrence list

val create_root :
  Nested_sequent.supply ->
  Symbolic_formula.t list ->
  t * Nested_sequent.position * Nested_sequent.supply

val find_occurrence :
  t ->
  Nested_sequent.occurrence_id ->
  formula_occurrence option

val formulas_at :
  t ->
  Nested_sequent.position ->
  formula_occurrence list

val add_formula :
  Nested_sequent.supply ->
  t ->
  Nested_sequent.position ->
  Symbolic_formula.t ->
  (t * formula_occurrence * Nested_sequent.supply) option

val remove_occurrence :
  t ->
  Nested_sequent.occurrence_id ->
  t option

val add_empty_child :
  Nested_sequent.supply ->
  t ->
  Nested_sequent.position ->
  Syntax.modal_index ->
  (t * Nested_sequent.position * Nested_sequent.supply) option

val positions :
  t ->
  Nested_sequent.position list

val has_position :
  t ->
  Nested_sequent.position ->
  bool

val equal :
  t ->
  t ->
  bool

val add_existing_formula :
  t ->
  Nested_sequent.position ->
  Nested_sequent.occurrence_id ->
  Symbolic_formula.t ->
  t option

val add_existing_empty_child :
  t ->
  Nested_sequent.position ->
  Syntax.modal_index ->
  Nested_sequent.position ->
  t option
