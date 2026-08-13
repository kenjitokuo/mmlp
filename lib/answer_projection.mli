type answer =
  (string * Syntax.term) list

val project :
  avoid:Substitution.String_set.t ->
  answer_representatives:
    (string * Symbolic_term.flexible_variable) list ->
  substitution:Symbolic_substitution.t ->
  (answer, string) result

val project_with_renaming :
  answer_representatives:
    (string * Symbolic_term.flexible_variable) list ->
  substitution:Symbolic_substitution.t ->
  renaming:
    (Symbolic_term.flexible_variable * string) list ->
  (answer, string) result
