type step = {
  source : Nested_sequent.position;
  label : Modal_symbol.t;
  target : Nested_sequent.position;
}

type t = {
  source : Nested_sequent.position;
  target : Nested_sequent.position;
  steps : step list;
}

val label : t -> Modal_symbol.t list

val empty_at : Nested_sequent.position -> t

val valid_step :
  Nested_sequent.t ->
  step ->
  bool

val valid :
  Nested_sequent.t ->
  t ->
  bool
