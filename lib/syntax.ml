type modal_index = Modal_index of int

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


let make_modal_index ~max_index i =
  if max_index < 1 then
    Error "modal index set must be nonempty"
  else if i < 1 || i > max_index then
    Error "modal index is outside the configured index set"
  else
    Ok (Modal_index i)

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

let compare_modal_index (Modal_index i) (Modal_index j) =
  Int.compare i j

let modal_index_number (Modal_index i) =
  i
