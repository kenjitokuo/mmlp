type rule =
  | Truth_axiom
  | Atomic_axiom
  | Or of Nested_sequent.occurrence_id
  | And of Nested_sequent.occurrence_id
  | Exists of Nested_sequent.occurrence_id * Syntax.term
  | Forall of Nested_sequent.occurrence_id * string
  | Box of Nested_sequent.occurrence_id * Nested_sequent.position
  | Diamond of
      Nested_sequent.occurrence_id
      * Nested_sequent.position
      * Modal_certificate.t
  | Seriality of
      Nested_sequent.position
      * Syntax.modal_index
      * Nested_sequent.position

type t = {
  conclusion : Nested_sequent.t;
  rule : rule;
  premises : t list;
}
