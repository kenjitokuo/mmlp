type t =
  | PosAtom of string * Symbolic_term.term list
  | NegAtom of string * Symbolic_term.term list
  | Bottom
  | Top
  | And of t * t
  | Or of t * t
  | Forall of string * t
  | Exists of string * t
  | Box of Syntax.modal_index * t
  | Diamond of Syntax.modal_index * t

val term_of_ordinary :
  Syntax.term ->
  Symbolic_term.term

val of_core_formula :
  Syntax.core_formula ->
  t

val substitute :
  string ->
  Symbolic_term.term ->
  t ->
  t

val apply_substitution :
  Symbolic_substitution.t ->
  t ->
  t

val proof_parameters :
  t ->
  Substitution.String_set.t

val retype_answers :
  (string * Symbolic_term.flexible_variable) list ->
  t ->
  t

val ordinary_variables_term :
  Symbolic_term.term ->
  Substitution.String_set.t

val ordinary_variables :
  t ->
  Substitution.String_set.t
