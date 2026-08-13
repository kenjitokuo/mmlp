type configuration

val of_root :
  Symbolic_root.t ->
  configuration

val state :
  configuration ->
  Symbolic_state.t

val active_eigenparameters :
  configuration ->
  Substitution.String_set.t

val nested_supply :
  configuration ->
  Nested_sequent.supply

val symbolic_supply :
  configuration ->
  Symbolic_term.supply

val node_id :
  configuration ->
  int

val serial_modalities :
  Modal_axiom.Set.t ->
  Syntax.modal_index list

type action =
  | Or_action of Nested_sequent.occurrence_id
  | And_action of Nested_sequent.occurrence_id
  | Exists_action of Nested_sequent.occurrence_id
  | Forall_action of Nested_sequent.occurrence_id * string
  | Box_action of Nested_sequent.occurrence_id
  | Diamond_action of
      Nested_sequent.occurrence_id
      * Nested_sequent.position
      * Modal_certificate.t
  | Seriality_action of
      Nested_sequent.position
      * Syntax.modal_index

val fresh_eigenparameter :
  configuration ->
  string

val available_actions :
  environment:Environment.t ->
  configuration ->
  action list

type transition =
  | Unary of
      Symbolic_derivation.rule
      * configuration
  | Binary of
      Symbolic_derivation.rule
      * configuration
      * configuration

val apply_action :
  environment:Environment.t ->
  configuration ->
  action ->
  transition option

val terminal_rules :
  configuration ->
  Symbolic_derivation.rule list

val derivations_within_depth :
  environment:Environment.t ->
  depth:int ->
  configuration ->
  Symbolic_derivation.t list

type solved_derivation = {
  derivation : Symbolic_derivation.t;
  substitution : Symbolic_substitution.t;
}

val solve_derivation :
  Symbolic_derivation.t ->
  solved_derivation option

val names_to_avoid :
  Symbolic_derivation.t ->
  Substitution.String_set.t

val project_solved_derivation :
  root:Symbolic_root.t ->
  solved_derivation ->
  (Answer_projection.answer, string) result

type computed_answer = {
  answer : Answer_projection.answer;
  derivation : Symbolic_derivation.t;
  substitution : Symbolic_substitution.t;
}

val answers_within_depth :
  environment:Environment.t ->
  root:Symbolic_root.t ->
  depth:int ->
  computed_answer list

val answers_at_exact_depth :
  environment:Environment.t ->
  root:Symbolic_root.t ->
  depth:int ->
  computed_answer list

val iterative_deepening :
  environment:Environment.t ->
  root:Symbolic_root.t ->
  computed_answer Seq.t

val allocated_proof_parameters :
  configuration ->
  Substitution.String_set.t

val with_allocated_proof_parameters :
  Substitution.String_set.t ->
  configuration ->
  configuration

type allocation_state

val allocation_state_of_configuration :
  configuration ->
  allocation_state

val with_allocation_state :
  allocation_state ->
  configuration ->
  configuration
