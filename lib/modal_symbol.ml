type t =
  | Forward of Syntax.modal_index
  | Backward of Syntax.modal_index

let converse = function
  | Forward i -> Backward i
  | Backward i -> Forward i

let compare a b =
  match a, b with
  | Forward i, Forward j
  | Backward i, Backward j ->
      Syntax.compare_modal_index i j
  | Forward _, Backward _ -> -1
  | Backward _, Forward _ -> 1

let converse_word word =
  List.rev_map converse word
