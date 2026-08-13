type output_substitution =
  (string * Syntax.term) list

let rec term_variables = function
  | Syntax.Var variable ->
      Substitution.String_set.singleton variable
  | Syntax.Param _
  | Syntax.Const _ ->
      Substitution.String_set.empty
  | Syntax.Fun (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          Substitution.String_set.union
            variables
            (term_variables argument))
        Substitution.String_set.empty
        arguments

let rec free_variables = function
  | Syntax.Atom (_, terms) ->
      List.fold_left
        (fun variables term ->
          Substitution.String_set.union
            variables
            (term_variables term))
        Substitution.String_set.empty
        terms
  | Syntax.Bottom ->
      Substitution.String_set.empty
  | Syntax.Not formula ->
      free_variables formula
  | Syntax.And (left, right)
  | Syntax.Or (left, right)
  | Syntax.Imp (left, right) ->
      Substitution.String_set.union
        (free_variables left)
        (free_variables right)
  | Syntax.Forall (variable, body)
  | Syntax.Exists (variable, body) ->
      Substitution.String_set.remove
        variable
        (free_variables body)
  | Syntax.Box (_, body)
  | Syntax.Diamond (_, body) ->
      free_variables body

let rec ordinary_output_term = function
  | Syntax.Var _
  | Syntax.Const _ ->
      true
  | Syntax.Param _ ->
      false
  | Syntax.Fun (_, arguments) ->
      List.for_all ordinary_output_term arguments

let rec lookup variable = function
  | [] ->
      None
  | (candidate, term) :: rest ->
      if String.equal variable candidate then
        Some term
      else
        lookup variable rest

let rec apply_once substitution = function
  | Syntax.Var variable as term ->
      begin
        match lookup variable substitution with
        | None ->
            term
        | Some replacement ->
            replacement
      end
  | Syntax.Param _ as term ->
      term
  | Syntax.Const _ as term ->
      term
  | Syntax.Fun (name, arguments) ->
      Syntax.Fun
        (name, List.map (apply_once substitution) arguments)

let apply substitution term =
  apply_once substitution term

let domain substitution =
  List.fold_left
    (fun variables (variable, _) ->
      Substitution.String_set.add variable variables)
    Substitution.String_set.empty
    substitution

let instantiate
    ~query
    ~answer_variables
    ~answer
    ~substitution =
  let answer_variable_set =
    List.fold_left
      (fun variables variable ->
        Substitution.String_set.add variable variables)
      Substitution.String_set.empty
      answer_variables
  in
  let protected =
    Substitution.String_set.diff
      (free_variables query)
      answer_variable_set
  in
  if
    not
      (Substitution.String_set.is_empty
         (Substitution.String_set.inter
            (domain substitution)
            protected))
  then
    Error
      "output substitution attempts to instantiate an original non-answer query variable"
  else if
    not
      (List.for_all
         (fun (_, term) ->
           ordinary_output_term term)
         substitution)
  then
    Error
      "output substitution contains a non-user proof term"
  else
    Ok
      (List.filter_map
         (fun variable ->
           match List.assoc_opt variable answer with
           | None ->
               None
           | Some term ->
               Some
                 (variable,
                  apply substitution term))
         answer_variables)
