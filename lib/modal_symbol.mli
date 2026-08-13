type t =
  | Forward of Syntax.modal_index
  | Backward of Syntax.modal_index

val converse : t -> t

val compare : t -> t -> int

val converse_word : t list -> t list
