val parse_term :
  string ->
  (Syntax.term, string) result

val parse_formula :
  max_modal_index:int ->
  string ->
  (Syntax.formula, string) result
