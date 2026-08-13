type t = {
  state : Symbolic_state.t;
  root_position : Nested_sequent.position;
  answer_representatives :
    (string * Symbolic_term.flexible_variable) list;
  nested_supply : Nested_sequent.supply;
  symbolic_supply : Symbolic_term.supply;
}

let rec free_variables_term = function
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
            (free_variables_term argument))
        Substitution.String_set.empty
        arguments

let rec free_variables = function
  | Syntax.Atom (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          Substitution.String_set.union
            variables
            (free_variables_term argument))
        Substitution.String_set.empty
        arguments
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

let universal_closure formula =
  let variables =
    Substitution.String_set.elements
      (free_variables formula)
  in
  List.fold_right
    (fun variable body ->
      Syntax.Forall (variable, body))
    variables
    formula

let validate_program environment program =
  let rec check = function
    | [] ->
        Ok ()
    | formula :: rest ->
        begin
          match
            Environment.validate_surface_formula
              environment
              formula
          with
          | Error message ->
              Error message
          | Ok () ->
              check rest
        end
  in
  check program

let validate_answer_variables query answer_variables =
  let free =
    free_variables query
  in
  let rec check seen = function
    | [] ->
        Ok ()
    | variable :: rest ->
        if Substitution.String_set.mem variable seen then
          Error "answer-role variables must be distinct"
        else if not (Substitution.String_set.mem variable free) then
          Error
            ("answer-role variable is not free in query: "
             ^ variable)
        else
          check
            (Substitution.String_set.add variable seen)
            rest
  in
  check Substitution.String_set.empty answer_variables

let create_answer_representatives
    symbolic_supply
    answer_variables =
  List.fold_left
    (fun (representatives, supply) variable ->
      let representative, supply =
        Symbolic_term.fresh_answer
          supply
          variable
      in
      (variable, representative) :: representatives,
      supply)
    ([], symbolic_supply)
    answer_variables
  |> fun (representatives, supply) ->
     List.rev representatives, supply

let create
    ~environment
    ~program
    ~query
    ~answer_variables =
  let program =
    List.map universal_closure program
  in
  match validate_program environment program with
  | Error message ->
      Error message
  | Ok () ->
      begin
        match
          Environment.validate_surface_formula
            environment
            query
        with
        | Error message ->
            Error message
        | Ok () ->
            begin
              match
                validate_answer_variables
                  query
                  answer_variables
              with
              | Error message ->
                  Error message
              | Ok () ->
                  let
                    answer_representatives,
                    symbolic_supply
                  =
                    create_answer_representatives
                      Symbolic_term.initial_supply
                      answer_variables
                  in
                  let program_formulas =
                    List.map
                      (fun formula ->
                        Symbolic_formula.of_core_formula
                          (Nnf.nnf_minus formula))
                      program
                  in
                  let query_formula =
                    Symbolic_formula.of_core_formula
                      (Nnf.nnf_plus query)
                    |> Symbolic_formula.retype_answers
                         answer_representatives
                  in
                  let initial_formulas =
                    match program_formulas with
                    | [] ->
                        [ Symbolic_formula.Bottom;
                          query_formula ]
                    | _ ->
                        program_formulas @ [query_formula]
                  in
                  let
                    state,
                    root_position,
                    nested_supply
                  =
                    Symbolic_state.create_root
                      Nested_sequent.initial_supply
                      initial_formulas
                  in
                  Ok
                    {
                      state;
                      root_position;
                      answer_representatives;
                      nested_supply;
                      symbolic_supply;
                    }
            end
      end

let state root =
  root.state

let root_position root =
  root.root_position

let answer_representatives root =
  root.answer_representatives

let nested_supply root =
  root.nested_supply

let symbolic_supply root =
  root.symbolic_supply
