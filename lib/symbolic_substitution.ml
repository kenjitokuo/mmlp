module Flexible_order = struct
  type t = Symbolic_term.flexible_variable

  let compare =
    Symbolic_term.compare_flexible
end

module Flexible_map = Map.Make (Flexible_order)

type t =
  Symbolic_term.term Flexible_map.t

let empty =
  Flexible_map.empty

let find_opt substitution flexible =
  Flexible_map.find_opt flexible substitution

let bindings substitution =
  Flexible_map.bindings substitution

let rec apply substitution term =
  match term with
  | Symbolic_term.Var _
  | Symbolic_term.Param _
  | Symbolic_term.Const _ ->
      term
  | Symbolic_term.Flex flexible ->
      begin
        match find_opt substitution flexible with
        | None ->
            term
        | Some replacement ->
            apply substitution replacement
      end
  | Symbolic_term.Fun (name, arguments) ->
      Symbolic_term.Fun
        (name, List.map (apply substitution) arguments)

let occurs flexible term =
  List.exists
    (Symbolic_term.equal_flexible flexible)
    (Symbolic_term.flexible_variables term)

let bind substitution flexible term =
  let term = apply substitution term in
  if occurs flexible term then
    None
  else
    let single =
      Flexible_map.singleton flexible term
    in
    let substitution =
      Flexible_map.map
        (apply single)
        substitution
    in
    Some (Flexible_map.add flexible term substitution)

let remove substitution flexible =
  Flexible_map.remove flexible substitution

let apply_postfix first second term =
  apply second (apply first term)
