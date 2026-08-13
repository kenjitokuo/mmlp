type residual_renaming =
  (Symbolic_term.flexible_variable * string) list

val concretize_term :
  substitution:Symbolic_substitution.t ->
  renaming:residual_renaming ->
  Symbolic_term.term ->
  (Syntax.term, string) result

val concretize_formula :
  substitution:Symbolic_substitution.t ->
  renaming:residual_renaming ->
  Symbolic_formula.t ->
  (Syntax.core_formula, string) result

val concretize_state :
  substitution:Symbolic_substitution.t ->
  renaming:residual_renaming ->
  Symbolic_state.t ->
  (Nested_sequent.t, string) result

val concretize :
  avoid:Substitution.String_set.t ->
  substitution:Symbolic_substitution.t ->
  Symbolic_derivation.t ->
  (residual_renaming * Derivation.t, string) result
