let rec term ~variable ~replacement = function
  | Syntax.Var x when String.equal x variable ->
      replacement
  | Syntax.Var x ->
      Syntax.Var x
  | Syntax.Param a ->
      Syntax.Param a
  | Syntax.Const c ->
      Syntax.Const c
  | Syntax.Fun (f, arguments) ->
      Syntax.Fun
        (f, List.map (term ~variable ~replacement) arguments)

module String_set = Set.Make (String)

let rec free_vars_term = function
  | Syntax.Var x ->
      String_set.singleton x
  | Syntax.Param _
  | Syntax.Const _ ->
      String_set.empty
  | Syntax.Fun (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          String_set.union variables (free_vars_term argument))
        String_set.empty
        arguments

let rec free_vars_core_formula = function
  | Syntax.PosAtom (_, arguments)
  | Syntax.NegAtom (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          String_set.union variables (free_vars_term argument))
        String_set.empty
        arguments
  | Syntax.CoreBottom
  | Syntax.CoreTop ->
      String_set.empty
  | Syntax.CoreAnd (a, b)
  | Syntax.CoreOr (a, b) ->
      String_set.union
        (free_vars_core_formula a)
        (free_vars_core_formula b)
  | Syntax.CoreForall (x, a)
  | Syntax.CoreExists (x, a) ->
      String_set.remove x (free_vars_core_formula a)
  | Syntax.CoreBox (_, a)
  | Syntax.CoreDiamond (_, a) ->
      free_vars_core_formula a

let rec vars_core_formula = function
  | Syntax.PosAtom (_, arguments)
  | Syntax.NegAtom (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          String_set.union variables (free_vars_term argument))
        String_set.empty
        arguments
  | Syntax.CoreBottom
  | Syntax.CoreTop ->
      String_set.empty
  | Syntax.CoreAnd (a, b)
  | Syntax.CoreOr (a, b) ->
      String_set.union
        (vars_core_formula a)
        (vars_core_formula b)
  | Syntax.CoreForall (x, a)
  | Syntax.CoreExists (x, a) ->
      String_set.add x (vars_core_formula a)
  | Syntax.CoreBox (_, a)
  | Syntax.CoreDiamond (_, a) ->
      vars_core_formula a

let fresh_variable ~base forbidden =
  let rec search n =
    let candidate = base ^ "_" ^ string_of_int n in
    if String_set.mem candidate forbidden then
      search (n + 1)
    else
      candidate
  in
  if String_set.mem base forbidden then search 0 else base

let rec core_formula ~variable ~replacement = function
  | Syntax.PosAtom (p, arguments) ->
      Syntax.PosAtom
        (p, List.map (term ~variable ~replacement) arguments)
  | Syntax.NegAtom (p, arguments) ->
      Syntax.NegAtom
        (p, List.map (term ~variable ~replacement) arguments)
  | Syntax.CoreBottom ->
      Syntax.CoreBottom
  | Syntax.CoreTop ->
      Syntax.CoreTop
  | Syntax.CoreAnd (a, b) ->
      Syntax.CoreAnd
        ( core_formula ~variable ~replacement a,
          core_formula ~variable ~replacement b )
  | Syntax.CoreOr (a, b) ->
      Syntax.CoreOr
        ( core_formula ~variable ~replacement a,
          core_formula ~variable ~replacement b )
  | Syntax.CoreForall (x, a) ->
      if String.equal x variable then
        Syntax.CoreForall (x, a)
      else if String_set.mem x (free_vars_term replacement) then
        let forbidden =
          String_set.add variable
            (String_set.union
               (vars_core_formula a)
               (free_vars_term replacement))
        in
        let fresh = fresh_variable ~base:x forbidden in
        let renamed =
          core_formula
            ~variable:x
            ~replacement:(Syntax.Var fresh)
            a
        in
        Syntax.CoreForall
          (fresh, core_formula ~variable ~replacement renamed)
      else
        Syntax.CoreForall
          (x, core_formula ~variable ~replacement a)
  | Syntax.CoreExists (x, a) ->
      if String.equal x variable then
        Syntax.CoreExists (x, a)
      else if String_set.mem x (free_vars_term replacement) then
        let forbidden =
          String_set.add variable
            (String_set.union
               (vars_core_formula a)
               (free_vars_term replacement))
        in
        let fresh = fresh_variable ~base:x forbidden in
        let renamed =
          core_formula
            ~variable:x
            ~replacement:(Syntax.Var fresh)
            a
        in
        Syntax.CoreExists
          (fresh, core_formula ~variable ~replacement renamed)
      else
        Syntax.CoreExists
          (x, core_formula ~variable ~replacement a)
  | Syntax.CoreBox (i, a) ->
      Syntax.CoreBox
        (i, core_formula ~variable ~replacement a)
  | Syntax.CoreDiamond (i, a) ->
      Syntax.CoreDiamond
        (i, core_formula ~variable ~replacement a)

let rec proof_params_term = function
  | Syntax.Var _
  | Syntax.Const _ ->
      String_set.empty
  | Syntax.Param a ->
      String_set.singleton a
  | Syntax.Fun (_, arguments) ->
      List.fold_left
        (fun parameters argument ->
          String_set.union parameters (proof_params_term argument))
        String_set.empty
        arguments

let rec proof_params_core_formula = function
  | Syntax.PosAtom (_, arguments)
  | Syntax.NegAtom (_, arguments) ->
      List.fold_left
        (fun parameters argument ->
          String_set.union parameters (proof_params_term argument))
        String_set.empty
        arguments
  | Syntax.CoreBottom
  | Syntax.CoreTop ->
      String_set.empty
  | Syntax.CoreAnd (a, b)
  | Syntax.CoreOr (a, b) ->
      String_set.union
        (proof_params_core_formula a)
        (proof_params_core_formula b)
  | Syntax.CoreForall (_, a)
  | Syntax.CoreExists (_, a)
  | Syntax.CoreBox (_, a)
  | Syntax.CoreDiamond (_, a) ->
      proof_params_core_formula a
