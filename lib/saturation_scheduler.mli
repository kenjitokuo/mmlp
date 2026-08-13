type obligation =
  | Or of Nested_sequent.occurrence_id
  | And of Nested_sequent.occurrence_id
  | Forall of Nested_sequent.occurrence_id
  | Exists of Nested_sequent.occurrence_id * int
  | Box of Nested_sequent.occurrence_id
  | Diamond of
      Nested_sequent.occurrence_id
      * Syntax.modal_index
      * Nested_sequent.position
      * Nested_sequent.position
  | Seriality of Syntax.modal_index * Nested_sequent.position

type configuration

type transition =
  | Closed of Derivation.t
  | Bookkeeping of configuration
  | Applied of {
      obligation : obligation;
      code : int;
      rule : Derivation.rule;
      successors : configuration list;
    }

val create :
  Nested_sequent.t ->
  configuration

val state :
  configuration ->
  Nested_sequent.t

val history :
  configuration ->
  int list

val stage :
  configuration ->
  int

val obligation_code :
  obligation ->
  int

val proof_term :
  Signature.t ->
  int ->
  Syntax.term

val available_obligations :
  environment:Environment.t ->
  configuration ->
  obligation list

val step :
  environment:Environment.t ->
  configuration ->
  (transition, string) result

val proof_within_steps :
  environment:Environment.t ->
  max_steps:int ->
  configuration ->
  Derivation.t option
