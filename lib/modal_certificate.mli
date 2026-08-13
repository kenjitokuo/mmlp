type t = {
  walk : Signed_walk.t;
  derivation : Grammar_derivation.t;
}

val valid :
  grammar:Grammar.Production_set.t ->
  sequent:Nested_sequent.t ->
  modality:Syntax.modal_index ->
  source:Nested_sequent.position ->
  target:Nested_sequent.position ->
  t ->
  bool
