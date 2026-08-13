open Syntax

let rec nnf_plus = function
  | Atom (p, ts) ->
      PosAtom (p, ts)
  | Bottom ->
      CoreBottom
  | Not a ->
      nnf_minus a
  | And (a, b) ->
      CoreAnd (nnf_plus a, nnf_plus b)
  | Or (a, b) ->
      CoreOr (nnf_plus a, nnf_plus b)
  | Imp (a, b) ->
      CoreOr (nnf_minus a, nnf_plus b)
  | Forall (x, a) ->
      CoreForall (x, nnf_plus a)
  | Exists (x, a) ->
      CoreExists (x, nnf_plus a)
  | Box (i, a) ->
      CoreBox (i, nnf_plus a)
  | Diamond (i, a) ->
      CoreDiamond (i, nnf_plus a)

and nnf_minus = function
  | Atom (p, ts) ->
      NegAtom (p, ts)
  | Bottom ->
      CoreTop
  | Not a ->
      nnf_plus a
  | And (a, b) ->
      CoreOr (nnf_minus a, nnf_minus b)
  | Or (a, b) ->
      CoreAnd (nnf_minus a, nnf_minus b)
  | Imp (a, b) ->
      CoreAnd (nnf_plus a, nnf_minus b)
  | Forall (x, a) ->
      CoreExists (x, nnf_minus a)
  | Exists (x, a) ->
      CoreForall (x, nnf_minus a)
  | Box (i, a) ->
      CoreDiamond (i, nnf_minus a)
  | Diamond (i, a) ->
      CoreBox (i, nnf_minus a)
