type prepared = {
  root : Symbolic_root.t;
  answers : Trusted_answer.t Seq.t;
}

val prepare :
  environment:Environment.t ->
  program:Syntax.formula list ->
  query:Syntax.formula ->
  answer_variables:string list ->
  (prepared, string) result

val answers_within_depth :
  environment:Environment.t ->
  program:Syntax.formula list ->
  query:Syntax.formula ->
  answer_variables:string list ->
  depth:int ->
  (Trusted_answer.t list, string) result

val answers_at_exact_depth :
  environment:Environment.t ->
  program:Syntax.formula list ->
  query:Syntax.formula ->
  answer_variables:string list ->
  depth:int ->
  (Trusted_answer.t list, string) result

val focused_answers_within_depth :
  environment:Environment.t ->
  program:Syntax.formula list ->
  query:Syntax.formula ->
  answer_variables:string list ->
  depth:int ->
  (Trusted_answer.t list, string) result

val focused_answers_at_exact_depth :
  environment:Environment.t ->
  program:Syntax.formula list ->
  query:Syntax.formula ->
  answer_variables:string list ->
  depth:int ->
  (Trusted_answer.t list, string) result

val prepare_focused :
  environment:Environment.t ->
  program:Syntax.formula list ->
  query:Syntax.formula ->
  answer_variables:string list ->
  (prepared, string) result

val instantiate_answer :
  query:Syntax.formula ->
  answer_variables:string list ->
  trusted:Trusted_answer.t ->
  substitution:Answer_instance.output_substitution ->
  ((string * Syntax.term) list, string) result
