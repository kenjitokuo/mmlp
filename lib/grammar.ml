type word = Modal_symbol.t list

type production = {
  lhs : word;
  rhs : word;
}

let converse_production p =
  {
    lhs = Modal_symbol.converse_word p.lhs;
    rhs = Modal_symbol.converse_word p.rhs;
  }

let base_production_of_axiom = function
  | Modal_axiom.D _ ->
      None
  | Modal_axiom.T i ->
      Some {
        lhs = [Modal_symbol.Forward i];
        rhs = [];
      }
  | Modal_axiom.I (i, j) ->
      Some {
        lhs = [Modal_symbol.Forward i];
        rhs = [Modal_symbol.Forward j];
      }
  | Modal_axiom.B (i, j) ->
      Some {
        lhs = [Modal_symbol.Backward j];
        rhs = [Modal_symbol.Forward i];
      }
  | Modal_axiom.Four (i, j, k) ->
      Some {
        lhs = [Modal_symbol.Forward i];
        rhs = [Modal_symbol.Forward j; Modal_symbol.Forward k];
      }
  | Modal_axiom.Five (i, j, k) ->
      Some {
        lhs = [Modal_symbol.Forward k];
        rhs = [Modal_symbol.Backward j; Modal_symbol.Forward i];
      }

let compare_word =
  List.compare Modal_symbol.compare

let compare_production p q =
  let c = compare_word p.lhs q.lhs in
  if c <> 0 then c else compare_word p.rhs q.rhs

module Production_set = Set.Make (struct
  type t = production
  let compare = compare_production
end)

let of_axioms axioms =
  Modal_axiom.Set.fold
    (fun axiom acc ->
      match base_production_of_axiom axiom with
      | None ->
          acc
      | Some p ->
          acc
          |> Production_set.add p
          |> Production_set.add (converse_production p))
    axioms
    Production_set.empty
