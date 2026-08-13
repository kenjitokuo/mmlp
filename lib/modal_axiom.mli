type t =
  | D of Syntax.modal_index
  | T of Syntax.modal_index
  | I of Syntax.modal_index * Syntax.modal_index
  | B of Syntax.modal_index * Syntax.modal_index
  | Four of Syntax.modal_index * Syntax.modal_index * Syntax.modal_index
  | Five of Syntax.modal_index * Syntax.modal_index * Syntax.modal_index

val compare : t -> t -> int

module Set : Stdlib.Set.S with type elt = t
