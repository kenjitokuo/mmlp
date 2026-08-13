val is_truth_axiom :
  Nested_sequent.t ->
  bool

val is_atomic_axiom :
  Nested_sequent.t ->
  bool

val apply_or :
  Nested_sequent.supply ->
  Nested_sequent.t ->
  Nested_sequent.occurrence_id ->
  (Nested_sequent.t
   * Nested_sequent.formula_occurrence
   * Nested_sequent.formula_occurrence
   * Nested_sequent.supply) option

val apply_and :
  Nested_sequent.supply ->
  Nested_sequent.t ->
  Nested_sequent.occurrence_id ->
  (Nested_sequent.t
   * Nested_sequent.formula_occurrence
   * Nested_sequent.t
   * Nested_sequent.formula_occurrence
   * Nested_sequent.supply) option

val apply_exists :
  Nested_sequent.supply ->
  Nested_sequent.t ->
  Nested_sequent.occurrence_id ->
  Syntax.term ->
  (Nested_sequent.t
   * Nested_sequent.formula_occurrence
   * Nested_sequent.supply) option

val apply_forall :
  Nested_sequent.supply ->
  Nested_sequent.t ->
  Nested_sequent.occurrence_id ->
  string ->
  (Nested_sequent.t
   * Nested_sequent.formula_occurrence
   * Nested_sequent.supply) option

val apply_box :
  Nested_sequent.supply ->
  Nested_sequent.t ->
  Nested_sequent.occurrence_id ->
  (Nested_sequent.t
   * Nested_sequent.position
   * Nested_sequent.formula_occurrence
   * Nested_sequent.supply) option

val apply_seriality :
  Nested_sequent.supply ->
  Modal_axiom.Set.t ->
  Nested_sequent.t ->
  Nested_sequent.position ->
  Syntax.modal_index ->
  (Nested_sequent.t
   * Nested_sequent.position
   * Nested_sequent.supply) option

val apply_diamond :
  Nested_sequent.supply ->
  Grammar.Production_set.t ->
  Nested_sequent.t ->
  Nested_sequent.occurrence_id ->
  Nested_sequent.position ->
  Modal_certificate.t ->
  (Nested_sequent.t
   * Nested_sequent.formula_occurrence
   * Nested_sequent.supply) option
