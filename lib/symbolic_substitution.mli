type t

val empty :
  t

val find_opt :
  t ->
  Symbolic_term.flexible_variable ->
  Symbolic_term.term option

val bindings :
  t ->
  (Symbolic_term.flexible_variable * Symbolic_term.term) list

val apply :
  t ->
  Symbolic_term.term ->
  Symbolic_term.term

val occurs :
  Symbolic_term.flexible_variable ->
  Symbolic_term.term ->
  bool

val bind :
  t ->
  Symbolic_term.flexible_variable ->
  Symbolic_term.term ->
  t option

val remove :
  t ->
  Symbolic_term.flexible_variable ->
  t

val apply_postfix :
  t ->
  t ->
  Symbolic_term.term ->
  Symbolic_term.term
