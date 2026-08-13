let rec is_truth_axiom sequent =
  List.exists
    (fun occurrence ->
      match occurrence.Nested_sequent.formula with
      | Syntax.CoreTop -> true
      | _ -> false)
    sequent.Nested_sequent.formulas
  ||
  List.exists
    (fun child -> is_truth_axiom child.Nested_sequent.subtree)
    sequent.Nested_sequent.children

let rec is_atomic_axiom sequent =
  let formulas = sequent.Nested_sequent.formulas in
  let rec has_opposite = function
    | [] -> false
    | occurrence :: rest ->
        let matched =
          match occurrence.Nested_sequent.formula with
          | Syntax.PosAtom (p, arguments) ->
              List.exists
                (fun other ->
                  other.Nested_sequent.formula
                  = Syntax.NegAtom (p, arguments))
                formulas
          | Syntax.NegAtom (p, arguments) ->
              List.exists
                (fun other ->
                  other.Nested_sequent.formula
                  = Syntax.PosAtom (p, arguments))
                formulas
          | _ ->
              false
        in
        matched || has_opposite rest
  in
  has_opposite formulas
  ||
  List.exists
    (fun child -> is_atomic_axiom child.Nested_sequent.subtree)
    sequent.Nested_sequent.children

let apply_or supply sequent occurrence_id =
  match Nested_sequent.find_occurrence sequent occurrence_id with
  | Some (position, occurrence) ->
      (match occurrence.Nested_sequent.formula with
       | Syntax.CoreOr (a, b) ->
           (match Nested_sequent.remove_occurrence sequent occurrence_id with
            | None ->
                None
            | Some sequent ->
                (match Nested_sequent.add_formula supply sequent position a with
                 | None ->
                     None
                 | Some (sequent, occurrence_a, supply) ->
                     (match Nested_sequent.add_formula supply sequent position b with
                      | None ->
                          None
                      | Some (sequent, occurrence_b, supply) ->
                          Some
                            ( sequent,
                              occurrence_a,
                              occurrence_b,
                              supply ))))
       | _ ->
           None)
  | None ->
      None

let apply_and supply sequent occurrence_id =
  match Nested_sequent.find_occurrence sequent occurrence_id with
  | Some (position, occurrence) ->
      (match occurrence.Nested_sequent.formula with
       | Syntax.CoreAnd (a, b) ->
           (match Nested_sequent.remove_occurrence sequent occurrence_id with
            | None ->
                None
            | Some base ->
                (match Nested_sequent.add_formula supply base position a with
                 | None ->
                     None
                 | Some (premise_a, occurrence_a, supply) ->
                     (match Nested_sequent.add_formula supply base position b with
                      | None ->
                          None
                      | Some (premise_b, occurrence_b, supply) ->
                          Some
                            ( premise_a,
                              occurrence_a,
                              premise_b,
                              occurrence_b,
                              supply ))))
       | _ ->
           None)
  | None ->
      None

let apply_exists supply sequent occurrence_id witness =
  match Nested_sequent.find_occurrence sequent occurrence_id with
  | Some (position, occurrence) ->
      (match occurrence.Nested_sequent.formula with
       | Syntax.CoreExists (variable, body) ->
           let instantiated =
             Substitution.core_formula
               ~variable
               ~replacement:witness
               body
           in
           (match
              Nested_sequent.add_formula
                supply
                sequent
                position
                instantiated
            with
            | None ->
                None
            | Some (sequent, new_occurrence, supply) ->
                Some (sequent, new_occurrence, supply))
       | _ ->
           None)
  | None ->
      None

let apply_forall supply sequent occurrence_id parameter =
  if
    Substitution.String_set.mem
      parameter
      (Nested_sequent.proof_params sequent)
  then
    None
  else
    match Nested_sequent.find_occurrence sequent occurrence_id with
    | Some (position, occurrence) ->
        (match occurrence.Nested_sequent.formula with
         | Syntax.CoreForall (variable, body) ->
             let instantiated =
               Substitution.core_formula
                 ~variable
                 ~replacement:(Syntax.Param parameter)
                 body
             in
             (match
                Nested_sequent.remove_occurrence
                  sequent
                  occurrence_id
              with
              | None ->
                  None
              | Some sequent ->
                  (match
                     Nested_sequent.add_formula
                       supply
                       sequent
                       position
                       instantiated
                   with
                   | None ->
                       None
                   | Some (sequent, new_occurrence, supply) ->
                       Some (sequent, new_occurrence, supply)))
         | _ ->
             None)
    | None ->
        None

let apply_box supply sequent occurrence_id =
  match Nested_sequent.find_occurrence sequent occurrence_id with
  | Some (position, occurrence) ->
      (match occurrence.Nested_sequent.formula with
       | Syntax.CoreBox (modality, body) ->
           (match
              Nested_sequent.remove_occurrence
                sequent
                occurrence_id
            with
            | None ->
                None
            | Some sequent ->
                (match
                   Nested_sequent.add_empty_child
                     supply
                     sequent
                     position
                     modality
                 with
                 | None ->
                     None
                 | Some (sequent, child_position, supply) ->
                     (match
                        Nested_sequent.add_formula
                          supply
                          sequent
                          child_position
                          body
                      with
                      | None ->
                          None
                      | Some (sequent, new_occurrence, supply) ->
                          Some
                            ( sequent,
                              child_position,
                              new_occurrence,
                              supply ))))
       | _ ->
           None)
  | None ->
      None

let apply_seriality supply axioms sequent parent modality =
  if Modal_axiom.Set.mem (Modal_axiom.D modality) axioms then
    Nested_sequent.add_empty_child
      supply
      sequent
      parent
      modality
  else
    None

let apply_diamond
    supply
    grammar
    sequent
    occurrence_id
    target
    certificate =
  match Nested_sequent.find_occurrence sequent occurrence_id with
  | Some (source, occurrence) ->
      (match occurrence.Nested_sequent.formula with
       | Syntax.CoreDiamond (modality, body) ->
           if
             Modal_certificate.valid
               ~grammar
               ~sequent
               ~modality
               ~source
               ~target
               certificate
           then
             (match
                Nested_sequent.add_formula
                  supply
                  sequent
                  target
                  body
              with
              | None ->
                  None
              | Some (sequent, new_occurrence, supply) ->
                  Some (sequent, new_occurrence, supply))
           else
             None
       | _ ->
           None)
  | None ->
      None
