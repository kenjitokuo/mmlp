type t = {
  answer : Answer_projection.answer;
  symbolic_derivation : Symbolic_derivation.t;
  ordinary_derivation : Derivation.t;
  substitution : Symbolic_substitution.t;
  residual_renaming : Proof_concretization.residual_renaming;
}

val certify :
  environment:Environment.t ->
  root:Symbolic_root.t ->
  Symbolic_search.solved_derivation ->
  (t, string) result
