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

(* Standardization apart of bound variables.

   The root answer replacement acts on the query after the usual
   standardization apart.  Bound variables of the program and of the
   query must not share a name with a free variable of the query:
   otherwise a witness metavariable that is later resolved to such a
   free variable would be captured by the binder when the symbolic
   derivation is concretized, and the reconstructed ordinary
   derivation would not prove the intended root. *)

let rec all_variables_term = function
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
            (all_variables_term argument))
        Substitution.String_set.empty
        arguments

let rec all_variables = function
  | Syntax.Atom (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          Substitution.String_set.union
            variables
            (all_variables_term argument))
        Substitution.String_set.empty
        arguments
  | Syntax.Bottom ->
      Substitution.String_set.empty
  | Syntax.Not formula
  | Syntax.Box (_, formula)
  | Syntax.Diamond (_, formula) ->
      all_variables formula
  | Syntax.And (left, right)
  | Syntax.Or (left, right)
  | Syntax.Imp (left, right) ->
      Substitution.String_set.union
        (all_variables left)
        (all_variables right)
  | Syntax.Forall (variable, body)
  | Syntax.Exists (variable, body) ->
      Substitution.String_set.add
        variable
        (all_variables body)

let rec rename_free_term ~variable ~replacement = function
  | Syntax.Var current when String.equal current variable ->
      Syntax.Var replacement
  | Syntax.Var _
  | Syntax.Param _
  | Syntax.Const _ as term ->
      term
  | Syntax.Fun (name, arguments) ->
      Syntax.Fun
        ( name,
          List.map
            (rename_free_term ~variable ~replacement)
            arguments )

(* The replacement name is globally fresh, so this renaming of free
   occurrences cannot be captured. *)
let rec rename_free ~variable ~replacement = function
  | Syntax.Atom (name, arguments) ->
      Syntax.Atom
        ( name,
          List.map
            (rename_free_term ~variable ~replacement)
            arguments )
  | Syntax.Bottom ->
      Syntax.Bottom
  | Syntax.Not formula ->
      Syntax.Not (rename_free ~variable ~replacement formula)
  | Syntax.And (left, right) ->
      Syntax.And
        ( rename_free ~variable ~replacement left,
          rename_free ~variable ~replacement right )
  | Syntax.Or (left, right) ->
      Syntax.Or
        ( rename_free ~variable ~replacement left,
          rename_free ~variable ~replacement right )
  | Syntax.Imp (left, right) ->
      Syntax.Imp
        ( rename_free ~variable ~replacement left,
          rename_free ~variable ~replacement right )
  | Syntax.Forall (bound, _)
  | Syntax.Exists (bound, _) as formula
    when String.equal bound variable ->
      formula
  | Syntax.Forall (bound, body) ->
      Syntax.Forall
        (bound, rename_free ~variable ~replacement body)
  | Syntax.Exists (bound, body) ->
      Syntax.Exists
        (bound, rename_free ~variable ~replacement body)
  | Syntax.Box (modality, body) ->
      Syntax.Box
        (modality, rename_free ~variable ~replacement body)
  | Syntax.Diamond (modality, body) ->
      Syntax.Diamond
        (modality, rename_free ~variable ~replacement body)

let fresh_bound_name base used =
  let rec search index =
    let candidate =
      base ^ "_" ^ string_of_int index
    in
    if Substitution.String_set.mem candidate used then
      search (index + 1)
    else
      candidate
  in
  search 0

(* Rename every binder whose name belongs to [forbidden].  The set
   [used] contains every name that must not be chosen as a new bound
   name; it is threaded so that all generated names are distinct. *)
let standardize_apart ~forbidden used formula =
  let rec go used = function
    | Syntax.Atom _
    | Syntax.Bottom as formula ->
        formula, used
    | Syntax.Not formula ->
        let formula, used = go used formula in
        Syntax.Not formula, used
    | Syntax.And (left, right) ->
        let left, used = go used left in
        let right, used = go used right in
        Syntax.And (left, right), used
    | Syntax.Or (left, right) ->
        let left, used = go used left in
        let right, used = go used right in
        Syntax.Or (left, right), used
    | Syntax.Imp (left, right) ->
        let left, used = go used left in
        let right, used = go used right in
        Syntax.Imp (left, right), used
    | Syntax.Box (modality, body) ->
        let body, used = go used body in
        Syntax.Box (modality, body), used
    | Syntax.Diamond (modality, body) ->
        let body, used = go used body in
        Syntax.Diamond (modality, body), used
    | Syntax.Forall (variable, body) ->
        let variable, body, used = binder used variable body in
        Syntax.Forall (variable, body), used
    | Syntax.Exists (variable, body) ->
        let variable, body, used = binder used variable body in
        Syntax.Exists (variable, body), used
  and binder used variable body =
    if Substitution.String_set.mem variable forbidden then
      let fresh = fresh_bound_name variable used in
      let used = Substitution.String_set.add fresh used in
      let body =
        rename_free ~variable ~replacement:fresh body
      in
      let body, used = go used body in
      fresh, body, used
    else
      let body, used = go used body in
      variable, body, used
  in
  go used formula

let standardize_root ~program ~query =
  let forbidden =
    free_variables query
  in
  let used =
    List.fold_left
      (fun used formula ->
        Substitution.String_set.union used (all_variables formula))
      (all_variables query)
      program
  in
  let program, used =
    List.fold_left
      (fun (formulas, used) formula ->
        let formula, used =
          standardize_apart ~forbidden used formula
        in
        formula :: formulas, used)
      ([], used)
      program
  in
  let query, _ =
    standardize_apart ~forbidden used query
  in
  List.rev program, query

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
                  let program, query =
                    standardize_root ~program ~query
                  in
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
