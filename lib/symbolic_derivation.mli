type rule =
  | Truth_leaf
  | Atomic_leaf of Symbolic_kernel.atomic_closure
  | Or of Nested_sequent.occurrence_id
  | And of Nested_sequent.occurrence_id
  | Exists of
      Nested_sequent.occurrence_id
      * Symbolic_term.flexible_variable
  | Forall of
      Nested_sequent.occurrence_id
      * string
  | Box of
      Nested_sequent.occurrence_id
      * Nested_sequent.position
  | Diamond of
      Nested_sequent.occurrence_id
      * Nested_sequent.position
      * Modal_certificate.t
  | Seriality of
      Nested_sequent.position
      * Syntax.modal_index
      * Nested_sequent.position

type t

val make :
  node_id:int ->
  conclusion:Symbolic_state.t ->
  rule:rule ->
  premises:t list ->
  t

val node_id :
  t ->
  int

val conclusion :
  t ->
  Symbolic_state.t

val rule :
  t ->
  rule

val premises :
  t ->
  t list

val atomic_constraints :
  t ->
  Scoped_unification.equation list

val height :
  t ->
  int

val check_global_eigenparameters :
  t ->
  bool

val check :
  environment:Environment.t ->
  t ->
  bool
