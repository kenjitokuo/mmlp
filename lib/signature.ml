module String_map = Map.Make (String)
module String_set = Set.Make (String)

type t = {
  predicates : int String_map.t;
  functions : int String_map.t;
  constants : String_set.t;
}

let empty =
  {
    predicates = String_map.empty;
    functions = String_map.empty;
    constants = String_set.empty;
  }

let add_arity table name arity =
  if name = "" then
    Error "symbol name must be nonempty"
  else if arity < 0 then
    Error "symbol arity must be nonnegative"
  else
    match String_map.find_opt name table with
    | None ->
        Ok (String_map.add name arity table)
    | Some existing when existing = arity ->
        Ok table
    | Some _ ->
        Error "symbol is already declared with a different arity"

let add_predicate signature name arity =
  match add_arity signature.predicates name arity with
  | Error message ->
      Error message
  | Ok predicates ->
      Ok { signature with predicates }

let add_function signature name arity =
  match add_arity signature.functions name arity with
  | Error message ->
      Error message
  | Ok functions ->
      Ok { signature with functions }

let add_constant signature name =
  if name = "" then
    Error "constant name must be nonempty"
  else
    Ok
      {
        signature with
        constants = String_set.add name signature.constants;
      }

let predicate_arity signature name =
  String_map.find_opt name signature.predicates

let function_arity signature name =
  String_map.find_opt name signature.functions

let has_constant signature name =
  String_set.mem name signature.constants

let rec validate_term signature = function
  | Syntax.Var _ ->
      Ok ()
  | Syntax.Param _ ->
      Ok ()
  | Syntax.Const name ->
      if has_constant signature name then
        Ok ()
      else
        Error ("undeclared constant: " ^ name)
  | Syntax.Fun (name, arguments) ->
      begin
        match function_arity signature name with
        | None ->
            Error ("undeclared function symbol: " ^ name)
        | Some arity ->
            if List.length arguments <> arity then
              Error
                ("function symbol has wrong arity: " ^ name)
            else
              let rec validate_arguments = function
                | [] ->
                    Ok ()
                | argument :: rest ->
                    begin
                      match validate_term signature argument with
                      | Error message ->
                          Error message
                      | Ok () ->
                          validate_arguments rest
                    end
              in
              validate_arguments arguments
      end

let validate_atom signature name arguments =
  match predicate_arity signature name with
  | None ->
      Error ("undeclared predicate symbol: " ^ name)
  | Some arity ->
      if List.length arguments <> arity then
        Error ("predicate symbol has wrong arity: " ^ name)
      else
        let rec validate_arguments = function
          | [] ->
              Ok ()
          | argument :: rest ->
              begin
                match validate_term signature argument with
                | Error message ->
                    Error message
                | Ok () ->
                    validate_arguments rest
              end
        in
        validate_arguments arguments

let rec validate_formula signature = function
  | Syntax.Atom (name, arguments) ->
      validate_atom signature name arguments
  | Syntax.Bottom ->
      Ok ()
  | Syntax.Not formula ->
      validate_formula signature formula
  | Syntax.And (left, right)
  | Syntax.Or (left, right)
  | Syntax.Imp (left, right) ->
      begin
        match validate_formula signature left with
        | Error message ->
            Error message
        | Ok () ->
            validate_formula signature right
      end
  | Syntax.Forall (_, body)
  | Syntax.Exists (_, body) ->
      validate_formula signature body
  | Syntax.Box (_, body)
  | Syntax.Diamond (_, body) ->
      validate_formula signature body

let rec validate_core_formula signature = function
  | Syntax.PosAtom (name, arguments)
  | Syntax.NegAtom (name, arguments) ->
      validate_atom signature name arguments
  | Syntax.CoreBottom
  | Syntax.CoreTop ->
      Ok ()
  | Syntax.CoreAnd (left, right)
  | Syntax.CoreOr (left, right) ->
      begin
        match validate_core_formula signature left with
        | Error message ->
            Error message
        | Ok () ->
            validate_core_formula signature right
      end
  | Syntax.CoreForall (_, body)
  | Syntax.CoreExists (_, body)
  | Syntax.CoreBox (_, body)
  | Syntax.CoreDiamond (_, body) ->
      validate_core_formula signature body

let constants signature =
  String_set.elements signature.constants

let functions signature =
  String_map.bindings signature.functions
