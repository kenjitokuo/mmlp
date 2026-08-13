open Syntax

type t =
  | D of modal_index
  | T of modal_index
  | I of modal_index * modal_index
  | B of modal_index * modal_index
  | Four of modal_index * modal_index * modal_index
  | Five of modal_index * modal_index * modal_index

let compare a b =
  match a, b with
  | D i, D j ->
      Syntax.compare_modal_index i j
  | D _, _ -> -1
  | _, D _ -> 1
  | T i, T j ->
      Syntax.compare_modal_index i j
  | T _, _ -> -1
  | _, T _ -> 1
  | I (i1, i2), I (j1, j2)
  | B (i1, i2), B (j1, j2) ->
      let c = Syntax.compare_modal_index i1 j1 in
      if c <> 0 then c else Syntax.compare_modal_index i2 j2
  | I _, _ -> -1
  | _, I _ -> 1
  | B _, _ -> -1
  | _, B _ -> 1
  | Four (i1, i2, i3), Four (j1, j2, j3)
  | Five (i1, i2, i3), Five (j1, j2, j3) ->
      let c1 = Syntax.compare_modal_index i1 j1 in
      if c1 <> 0 then c1
      else
        let c2 = Syntax.compare_modal_index i2 j2 in
        if c2 <> 0 then c2 else Syntax.compare_modal_index i3 j3
  | Four _, _ -> -1
  | _, Four _ -> 1

module Set = Set.Make (struct
  type nonrec t = t
  let compare = compare
end)
