type output_substitution =
  (string * Syntax.term) list

val instantiate :
  query:Syntax.formula ->
  answer_variables:string list ->
  answer:(string * Syntax.term) list ->
  substitution:output_substitution ->
  ((string * Syntax.term) list, string) result
