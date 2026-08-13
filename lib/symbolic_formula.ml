type t =
  | PosAtom of string * Symbolic_term.term list
  | NegAtom of string * Symbolic_term.term list
  | Bottom
  | Top
  | And of t * t
  | Or of t * t
  | Forall of string * t
  | Exists of string * t
  | Box of Syntax.modal_index * t
  | Diamond of Syntax.modal_index * t

let rec term_of_ordinary = function
  | Syntax.Var variable ->
      Symbolic_term.Var variable
  | Syntax.Param parameter ->
      Symbolic_term.Param parameter
  | Syntax.Const constant ->
      Symbolic_term.Const constant
  | Syntax.Fun (name, arguments) ->
      Symbolic_term.Fun
        (name, List.map term_of_ordinary arguments)

let rec of_core_formula = function
  | Syntax.PosAtom (name, arguments) ->
      PosAtom
        (name, List.map term_of_ordinary arguments)
  | Syntax.NegAtom (name, arguments) ->
      NegAtom
        (name, List.map term_of_ordinary arguments)
  | Syntax.CoreBottom ->
      Bottom
  | Syntax.CoreTop ->
      Top
  | Syntax.CoreAnd (left, right) ->
      And
        (of_core_formula left, of_core_formula right)
  | Syntax.CoreOr (left, right) ->
      Or
        (of_core_formula left, of_core_formula right)
  | Syntax.CoreForall (variable, body) ->
      Forall
        (variable, of_core_formula body)
  | Syntax.CoreExists (variable, body) ->
      Exists
        (variable, of_core_formula body)
  | Syntax.CoreBox (modality, body) ->
      Box
        (modality, of_core_formula body)
  | Syntax.CoreDiamond (modality, body) ->
      Diamond
        (modality, of_core_formula body)

let rec substitute_term variable replacement = function
  | Symbolic_term.Var current when String.equal current variable ->
      replacement
  | Symbolic_term.Var _
  | Symbolic_term.Param _
  | Symbolic_term.Flex _
  | Symbolic_term.Const _ as term ->
      term
  | Symbolic_term.Fun (name, arguments) ->
      Symbolic_term.Fun
        ( name,
          List.map
            (substitute_term variable replacement)
            arguments )

let rec substitute variable replacement = function
  | PosAtom (name, arguments) ->
      PosAtom
        ( name,
          List.map
            (substitute_term variable replacement)
            arguments )
  | NegAtom (name, arguments) ->
      NegAtom
        ( name,
          List.map
            (substitute_term variable replacement)
            arguments )
  | Bottom ->
      Bottom
  | Top ->
      Top
  | And (left, right) ->
      And
        ( substitute variable replacement left,
          substitute variable replacement right )
  | Or (left, right) ->
      Or
        ( substitute variable replacement left,
          substitute variable replacement right )
  | Forall (bound, body) when String.equal bound variable ->
      Forall (bound, body)
  | Exists (bound, body) when String.equal bound variable ->
      Exists (bound, body)
  | Forall (bound, body) ->
      Forall
        (bound, substitute variable replacement body)
  | Exists (bound, body) ->
      Exists
        (bound, substitute variable replacement body)
  | Box (modality, body) ->
      Box
        (modality, substitute variable replacement body)
  | Diamond (modality, body) ->
      Diamond
        (modality, substitute variable replacement body)

let rec apply_substitution substitution = function
  | PosAtom (name, arguments) ->
      PosAtom
        ( name,
          List.map
            (Symbolic_substitution.apply substitution)
            arguments )
  | NegAtom (name, arguments) ->
      NegAtom
        ( name,
          List.map
            (Symbolic_substitution.apply substitution)
            arguments )
  | Bottom ->
      Bottom
  | Top ->
      Top
  | And (left, right) ->
      And
        ( apply_substitution substitution left,
          apply_substitution substitution right )
  | Or (left, right) ->
      Or
        ( apply_substitution substitution left,
          apply_substitution substitution right )
  | Forall (variable, body) ->
      Forall
        (variable, apply_substitution substitution body)
  | Exists (variable, body) ->
      Exists
        (variable, apply_substitution substitution body)
  | Box (modality, body) ->
      Box
        (modality, apply_substitution substitution body)
  | Diamond (modality, body) ->
      Diamond
        (modality, apply_substitution substitution body)
let rec proof_parameters = function
  | PosAtom (_, arguments)
  | NegAtom (_, arguments) ->
      List.fold_left
        (fun parameters argument ->
          Substitution.String_set.union
            parameters
            (Symbolic_term.proof_parameters argument))
        Substitution.String_set.empty
        arguments
  | Bottom
  | Top ->
      Substitution.String_set.empty
  | And (left, right)
  | Or (left, right) ->
      Substitution.String_set.union
        (proof_parameters left)
        (proof_parameters right)
  | Forall (_, body)
  | Exists (_, body)
  | Box (_, body)
  | Diamond (_, body) ->
      proof_parameters body
let retype_answers answer_representatives formula =
  let find_answer variable =
    List.assoc_opt variable answer_representatives
  in
  let rec retype_term bound = function
    | Symbolic_term.Var variable ->
        if Substitution.String_set.mem variable bound then
          Symbolic_term.Var variable
        else
          begin
            match find_answer variable with
            | None ->
                Symbolic_term.Var variable
            | Some representative ->
                Symbolic_term.Flex representative
          end
    | Symbolic_term.Param parameter ->
        Symbolic_term.Param parameter
    | Symbolic_term.Flex flexible ->
        Symbolic_term.Flex flexible
    | Symbolic_term.Const constant ->
        Symbolic_term.Const constant
    | Symbolic_term.Fun (name, arguments) ->
        Symbolic_term.Fun
          ( name,
            List.map
              (retype_term bound)
              arguments )
  in
  let rec retype_formula bound = function
    | PosAtom (name, arguments) ->
        PosAtom
          ( name,
            List.map
              (retype_term bound)
              arguments )
    | NegAtom (name, arguments) ->
        NegAtom
          ( name,
            List.map
              (retype_term bound)
              arguments )
    | Bottom ->
        Bottom
    | Top ->
        Top
    | And (left, right) ->
        And
          ( retype_formula bound left,
            retype_formula bound right )
    | Or (left, right) ->
        Or
          ( retype_formula bound left,
            retype_formula bound right )
    | Forall (variable, body) ->
        Forall
          ( variable,
            retype_formula
              (Substitution.String_set.add
                 variable
                 bound)
              body )
    | Exists (variable, body) ->
        Exists
          ( variable,
            retype_formula
              (Substitution.String_set.add
                 variable
                 bound)
              body )
    | Box (modality, body) ->
        Box
          (modality, retype_formula bound body)
    | Diamond (modality, body) ->
        Diamond
          (modality, retype_formula bound body)
  in
  retype_formula
    Substitution.String_set.empty
    formula
let rec ordinary_variables_term = function
  | Symbolic_term.Var variable ->
      Substitution.String_set.singleton variable
  | Symbolic_term.Param _
  | Symbolic_term.Flex _
  | Symbolic_term.Const _ ->
      Substitution.String_set.empty
  | Symbolic_term.Fun (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          Substitution.String_set.union
            variables
            (ordinary_variables_term argument))
        Substitution.String_set.empty
        arguments

let rec ordinary_variables = function
  | PosAtom (_, arguments)
  | NegAtom (_, arguments) ->
      List.fold_left
        (fun variables argument ->
          Substitution.String_set.union
            variables
            (ordinary_variables_term argument))
        Substitution.String_set.empty
        arguments
  | Bottom
  | Top ->
      Substitution.String_set.empty
  | And (left, right)
  | Or (left, right) ->
      Substitution.String_set.union
        (ordinary_variables left)
        (ordinary_variables right)
  | Forall (variable, body)
  | Exists (variable, body) ->
      Substitution.String_set.add
        variable
        (ordinary_variables body)
  | Box (_, body)
  | Diamond (_, body) ->
      ordinary_variables body
