type modal_index

val make_modal_index :
  max_index:int -> int -> (modal_index, string) result

type term =
  | Var of string
  | Param of string
  | Const of string
  | Fun of string * term list

type formula =
  | Atom of string * term list
  | Bottom
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Forall of string * formula
  | Exists of string * formula
  | Box of modal_index * formula
  | Diamond of modal_index * formula

type core_formula =
  | PosAtom of string * term list
  | NegAtom of string * term list
  | CoreBottom
  | CoreTop
  | CoreAnd of core_formula * core_formula
  | CoreOr of core_formula * core_formula
  | CoreForall of string * core_formula
  | CoreExists of string * core_formula
  | CoreBox of modal_index * core_formula
  | CoreDiamond of modal_index * core_formula

val compare_modal_index : modal_index -> modal_index -> int


val modal_index_number :
  modal_index ->
  int
