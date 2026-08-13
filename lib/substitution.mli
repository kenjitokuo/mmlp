val term :
  variable:string ->
  replacement:Syntax.term ->
  Syntax.term ->
  Syntax.term

module String_set : Set.S with type elt = string

val free_vars_term :
  Syntax.term ->
  String_set.t

val free_vars_core_formula :
  Syntax.core_formula ->
  String_set.t

val vars_core_formula :
  Syntax.core_formula ->
  String_set.t

val core_formula :
  variable:string ->
  replacement:Syntax.term ->
  Syntax.core_formula ->
  Syntax.core_formula

val proof_params_term :
  Syntax.term ->
  String_set.t

val proof_params_core_formula :
  Syntax.core_formula ->
  String_set.t
