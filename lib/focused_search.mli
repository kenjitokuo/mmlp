val derivations_within_depth :
  environment:Environment.t ->
  depth:int ->
  Symbolic_search.configuration ->
  Symbolic_derivation.t list

val solve_derivation :
  Symbolic_derivation.t ->
  Symbolic_search.solved_derivation option

val answers_within_depth :
  environment:Environment.t ->
  root:Symbolic_root.t ->
  depth:int ->
  Trusted_answer.t list

val answers_at_exact_depth :
  environment:Environment.t ->
  root:Symbolic_root.t ->
  depth:int ->
  Trusted_answer.t list

val iterative_deepening :
  environment:Environment.t ->
  root:Symbolic_root.t ->
  Trusted_answer.t Seq.t
