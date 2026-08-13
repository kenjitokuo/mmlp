val certify_derivation :
  environment:Environment.t ->
  root:Symbolic_root.t ->
  Symbolic_derivation.t ->
  Trusted_answer.t option

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
