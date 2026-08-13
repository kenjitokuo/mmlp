type t = {
  max_modal_index : int;
  signature : Signature.t;
  axioms : Modal_axiom.Set.t;
}

let modal_index_in_range max_modal_index modality =
  let index =
    Syntax.modal_index_number modality
  in
  index >= 1 && index <= max_modal_index

let axiom_indices = function
  | Modal_axiom.D i
  | Modal_axiom.T i ->
      [i]
  | Modal_axiom.I (i, j)
  | Modal_axiom.B (i, j) ->
      [i; j]
  | Modal_axiom.Four (i, j, k)
  | Modal_axiom.Five (i, j, k) ->
      [i; j; k]

let axioms_in_range max_modal_index axioms =
  Modal_axiom.Set.for_all
    (fun axiom ->
      List.for_all
        (modal_index_in_range max_modal_index)
        (axiom_indices axiom))
    axioms

let create ~max_modal_index ~signature ~axioms =
  if max_modal_index < 1 then
    Error "maximal modal index must be positive"
  else if
    not (axioms_in_range max_modal_index axioms)
  then
    Error
      "selected modal axiom contains an index outside the configured index set"
  else
    Ok
      {
        max_modal_index;
        signature;
        axioms;
      }

let max_modal_index environment =
  environment.max_modal_index

let signature environment =
  environment.signature

let axioms environment =
  environment.axioms

let make_modal_index environment index =
  Syntax.make_modal_index
    ~max_index:environment.max_modal_index
    index

let grammar environment =
  Grammar.of_axioms environment.axioms

let rec surface_term_is_user_term = function
  | Syntax.Var _
  | Syntax.Const _ ->
      true
  | Syntax.Param _ ->
      false
  | Syntax.Fun (_, arguments) ->
      List.for_all
        surface_term_is_user_term
        arguments

let rec surface_formula_uses_user_terms = function
  | Syntax.Atom (_, arguments) ->
      List.for_all
        surface_term_is_user_term
        arguments
  | Syntax.Bottom ->
      true
  | Syntax.Not formula ->
      surface_formula_uses_user_terms formula
  | Syntax.And (left, right)
  | Syntax.Or (left, right)
  | Syntax.Imp (left, right) ->
      surface_formula_uses_user_terms left
      && surface_formula_uses_user_terms right
  | Syntax.Forall (_, body)
  | Syntax.Exists (_, body) ->
      surface_formula_uses_user_terms body
  | Syntax.Box (_, body)
  | Syntax.Diamond (_, body) ->
      surface_formula_uses_user_terms body

let rec surface_formula_modal_indices_valid
    environment =
  function
  | Syntax.Atom _
  | Syntax.Bottom ->
      true
  | Syntax.Not formula ->
      surface_formula_modal_indices_valid
        environment
        formula
  | Syntax.And (left, right)
  | Syntax.Or (left, right)
  | Syntax.Imp (left, right) ->
      surface_formula_modal_indices_valid
        environment
        left
      && surface_formula_modal_indices_valid
           environment
           right
  | Syntax.Forall (_, body)
  | Syntax.Exists (_, body) ->
      surface_formula_modal_indices_valid
        environment
        body
  | Syntax.Box (modality, body)
  | Syntax.Diamond (modality, body) ->
      modal_index_in_range
        environment.max_modal_index
        modality
      && surface_formula_modal_indices_valid
           environment
           body

let validate_surface_formula environment formula =
  match
    Signature.validate_formula
      environment.signature
      formula
  with
  | Error message ->
      Error message
  | Ok () ->
      if
        not (surface_formula_uses_user_terms formula)
      then
        Error
          "surface formula contains an internal proof parameter"
      else if
        not
          (surface_formula_modal_indices_valid
             environment
             formula)
      then
        Error
          "surface formula contains a modal index outside the configured index set"
      else
        Ok ()

let rec core_formula_modal_indices_valid
    environment =
  function
  | Syntax.PosAtom _
  | Syntax.NegAtom _
  | Syntax.CoreBottom
  | Syntax.CoreTop ->
      true
  | Syntax.CoreAnd (left, right)
  | Syntax.CoreOr (left, right) ->
      core_formula_modal_indices_valid
        environment
        left
      && core_formula_modal_indices_valid
           environment
           right
  | Syntax.CoreForall (_, body)
  | Syntax.CoreExists (_, body) ->
      core_formula_modal_indices_valid
        environment
        body
  | Syntax.CoreBox (modality, body)
  | Syntax.CoreDiamond (modality, body) ->
      modal_index_in_range
        environment.max_modal_index
        modality
      && core_formula_modal_indices_valid
           environment
           body

let rec configured_sequent environment sequent =
  List.for_all
    (fun occurrence ->
      core_formula_modal_indices_valid
        environment
        occurrence.Nested_sequent.formula)
    sequent.Nested_sequent.formulas
  &&
  List.for_all
    (fun child ->
      modal_index_in_range
        environment.max_modal_index
        child.Nested_sequent.modality
      && configured_sequent
           environment
           child.Nested_sequent.subtree)
    sequent.Nested_sequent.children

let check_derivation environment derivation =
  let rec configured node =
    configured_sequent
      environment
      node.Derivation.conclusion
    && List.for_all
         configured
         node.Derivation.premises
  in
  configured derivation
  &&
  Proof_checker.valid
    ~signature:environment.signature
    ~axioms:environment.axioms
    derivation
