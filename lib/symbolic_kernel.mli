type atomic_closure = {
  positive_occurrence : Nested_sequent.occurrence_id;
  negative_occurrence : Nested_sequent.occurrence_id;
  equations : Scoped_unification.equation list;
}

val proof_parameters :
  Symbolic_state.t ->
  Substitution.String_set.t

val is_truth_axiom :
  Symbolic_state.t ->
  bool

val atomic_closures :
  Symbolic_state.t ->
  atomic_closure list

val apply_or :
  Nested_sequent.supply ->
  Symbolic_state.t ->
  Nested_sequent.occurrence_id ->
  (Symbolic_state.t
   * Symbolic_state.formula_occurrence
   * Symbolic_state.formula_occurrence
   * Nested_sequent.supply) option

val apply_and :
  Nested_sequent.supply ->
  Symbolic_state.t ->
  Nested_sequent.occurrence_id ->
  (Symbolic_state.t
   * Symbolic_state.formula_occurrence
   * Symbolic_state.t
   * Symbolic_state.formula_occurrence
   * Nested_sequent.supply) option

val apply_exists :
  Nested_sequent.supply ->
  Symbolic_term.supply ->
  Symbolic_state.t ->
  Nested_sequent.occurrence_id ->
  active_eigenparameters:Substitution.String_set.t ->
  birth_node:int ->
  (Symbolic_state.t
   * Symbolic_state.formula_occurrence
   * Symbolic_term.flexible_variable
   * Nested_sequent.supply
   * Symbolic_term.supply) option

val apply_forall :
  Nested_sequent.supply ->
  Symbolic_state.t ->
  Nested_sequent.occurrence_id ->
  string ->
  (Symbolic_state.t
   * Symbolic_state.formula_occurrence
   * Nested_sequent.supply) option

val apply_box :
  Nested_sequent.supply ->
  Symbolic_state.t ->
  Nested_sequent.occurrence_id ->
  (Symbolic_state.t
   * Nested_sequent.position
   * Symbolic_state.formula_occurrence
   * Nested_sequent.supply) option

val apply_diamond :
  Nested_sequent.supply ->
  Grammar.Production_set.t ->
  Symbolic_state.t ->
  Nested_sequent.occurrence_id ->
  Nested_sequent.position ->
  Modal_certificate.t ->
  (Symbolic_state.t
   * Symbolic_state.formula_occurrence
   * Nested_sequent.supply) option

val apply_seriality :
  Nested_sequent.supply ->
  Modal_axiom.Set.t ->
  Symbolic_state.t ->
  Nested_sequent.position ->
  Syntax.modal_index ->
  (Symbolic_state.t
   * Nested_sequent.position
   * Nested_sequent.supply) option
