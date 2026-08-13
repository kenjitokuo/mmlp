type flexible_kind =
  | Answer of string
  | Witness
  | Auxiliary

type flexible_variable = {
  id : int;
  kind : flexible_kind;
  permission : Substitution.String_set.t;
  birth_node : int option;
}

type term =
  | Var of string
  | Param of string
  | Flex of flexible_variable
  | Const of string
  | Fun of string * term list

type supply = int

let initial_supply = 0

let fresh_answer supply variable =
  let flexible =
    {
      id = supply;
      kind = Answer variable;
      permission = Substitution.String_set.empty;
      birth_node = None;
    }
  in
  flexible, supply + 1

let fresh_meta supply ~active_eigenparameters ~birth_node =
  let flexible =
    {
      id = supply;
      kind = Witness;
      permission = active_eigenparameters;
      birth_node = Some birth_node;
    }
  in
  flexible, supply + 1

let fresh_restriction supply ~permission =
  let flexible =
    {
      id = supply;
      kind = Auxiliary;
      permission;
      birth_node = None;
    }
  in
  flexible, supply + 1

let compare_kind left right =
  match left, right with
  | Answer left_name, Answer right_name ->
      String.compare left_name right_name
  | Answer _, _ ->
      -1
  | _, Answer _ ->
      1
  | Witness, Witness ->
      0
  | Witness, Auxiliary ->
      -1
  | Auxiliary, Witness ->
      1
  | Auxiliary, Auxiliary ->
      0

let compare_flexible left right =
  match Int.compare left.id right.id with
  | result when result <> 0 ->
      result
  | _ ->
      begin
        match compare_kind left.kind right.kind with
        | result when result <> 0 ->
            result
        | _ ->
            Stdlib.compare left.birth_node right.birth_node
      end
let equal_flexible left right =
  compare_flexible left right = 0

let permission flexible =
  flexible.permission

let kind flexible =
  flexible.kind

let birth_node flexible =
  flexible.birth_node

let rec proof_parameters = function
  | Var _
  | Flex _
  | Const _ ->
      Substitution.String_set.empty
  | Param parameter ->
      Substitution.String_set.singleton parameter
  | Fun (_, arguments) ->
      List.fold_left
        (fun parameters argument ->
          Substitution.String_set.union
            parameters
            (proof_parameters argument))
        Substitution.String_set.empty
        arguments

let rec flexible_variables = function
  | Var _
  | Param _
  | Const _ ->
      []
  | Flex flexible ->
      [flexible]
  | Fun (_, arguments) ->
      List.concat_map flexible_variables arguments

let safe_for flexible term =
  Substitution.String_set.subset
    (proof_parameters term)
    flexible.permission
  &&
  List.for_all
    (fun dependency ->
      Substitution.String_set.subset
        dependency.permission
        flexible.permission)
    (flexible_variables term)




let fresh_answer_with_permission supply variable ~permission =
  let flexible =
    {
      id = supply;
      kind = Answer variable;
      permission;
      birth_node = None;
    }
  in
  flexible, supply + 1

let fresh_auxiliary supply ~permission =
  let flexible =
    {
      id = supply;
      kind = Auxiliary;
      permission;
      birth_node = None;
    }
  in
  flexible, supply + 1


let supply_after flexibles =
  List.fold_left
    (fun supply flexible ->
      max supply (flexible.id + 1))
    initial_supply
    flexibles
