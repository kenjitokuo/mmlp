type t

val create :
  environment:Environment.t ->
  program:Syntax.formula list ->
  query:Syntax.formula ->
  answer_variables:string list ->
  (t, string) result

val state :
  t ->
  Symbolic_state.t

val root_position :
  t ->
  Nested_sequent.position

val answer_representatives :
  t ->
  (string * Symbolic_term.flexible_variable) list

val nested_supply :
  t ->
  Nested_sequent.supply

val symbolic_supply :
  t ->
  Symbolic_term.supply
