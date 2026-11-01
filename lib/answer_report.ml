type answer =
  (string * Syntax.term) list

module String_set = Substitution.String_set

let rec term_variables = function
  | Syntax.Var variable ->
      String_set.singleton variable
  | Syntax.Param _
  | Syntax.Const _ ->
      String_set.empty
  | Syntax.Fun (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          String_set.union variables (term_variables argument))
        String_set.empty
        arguments

let rec free_variables = function
  | Syntax.Atom (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          String_set.union variables (term_variables argument))
        String_set.empty
        arguments
  | Syntax.Bottom ->
      String_set.empty
  | Syntax.Not formula
  | Syntax.Box (_, formula)
  | Syntax.Diamond (_, formula) ->
      free_variables formula
  | Syntax.And (left, right)
  | Syntax.Or (left, right)
  | Syntax.Imp (left, right) ->
      String_set.union (free_variables left) (free_variables right)
  | Syntax.Forall (variable, body)
  | Syntax.Exists (variable, body) ->
      String_set.remove variable (free_variables body)

let rigid_variables ~query ~answer_variables =
  String_set.diff
    (free_variables query)
    (String_set.of_list answer_variables)

let rec ordinary_user_term = function
  | Syntax.Var _
  | Syntax.Const _ ->
      true
  | Syntax.Param _ ->
      false
  | Syntax.Fun (_, arguments) ->
      List.for_all ordinary_user_term arguments

(* One-way matching.  Object variables outside [rigid] are pattern
   variables, and every other symbol must coincide.  The binding maps
   each pattern variable to the unique subterm it must denote. *)
let rec match_term ~rigid binding pattern target =
  match pattern with
  | Syntax.Var variable when not (String_set.mem variable rigid) ->
      begin
        match List.assoc_opt variable binding with
        | Some image ->
            if image = target then Some binding else None
        | None ->
            if ordinary_user_term target then
              Some ((variable, target) :: binding)
            else
              None
      end
  | Syntax.Var _
  | Syntax.Param _
  | Syntax.Const _ ->
      if pattern = target then Some binding else None
  | Syntax.Fun (name, arguments) ->
      begin
        match target with
        | Syntax.Fun (target_name, target_arguments)
          when String.equal name target_name
               && List.length arguments = List.length target_arguments ->
            List.fold_left2
              (fun binding argument target_argument ->
                match binding with
                | None ->
                    None
                | Some binding ->
                    match_term ~rigid binding argument target_argument)
              (Some binding)
              arguments
              target_arguments
        | _ ->
            None
      end

let value answer variable =
  match List.assoc_opt variable answer with
  | Some term -> term
  | None -> Syntax.Var variable

let output_instance ~rigid ~answer_variables ~general ~specific =
  List.fold_left
    (fun binding variable ->
      match binding with
      | None ->
          None
      | Some binding ->
          match_term
            ~rigid
            binding
            (value general variable)
            (value specific variable))
    (Some [])
    answer_variables
  <> None

let report ~rigid ~answer_variables ~answer_of items =
  List.fold_left
    (fun reported item ->
      let specific = answer_of item in
      if
        List.exists
          (fun earlier ->
            output_instance
              ~rigid
              ~answer_variables
              ~general:(answer_of earlier)
              ~specific)
          reported
      then
        reported
      else
        item :: reported)
    []
    items
  |> List.rev
