type t

val empty : t

val add_predicate :
  t ->
  string ->
  int ->
  (t, string) result

val add_function :
  t ->
  string ->
  int ->
  (t, string) result

val add_constant :
  t ->
  string ->
  (t, string) result

val predicate_arity :
  t ->
  string ->
  int option

val function_arity :
  t ->
  string ->
  int option

val has_constant :
  t ->
  string ->
  bool

val validate_term :
  t ->
  Syntax.term ->
  (unit, string) result

val validate_formula :
  t ->
  Syntax.formula ->
  (unit, string) result

val validate_core_formula :
  t ->
  Syntax.core_formula ->
  (unit, string) result

val constants :
  t ->
  string list

val functions :
  t ->
  (string * int) list
