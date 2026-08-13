type atomic_closure = {
  positive_occurrence : Nested_sequent.occurrence_id;
  negative_occurrence : Nested_sequent.occurrence_id;
  equations : Scoped_unification.equation list;
}

let proof_parameters state =
  List.fold_left
    (fun parameters occurrence ->
      Substitution.String_set.union
        parameters
        (Symbolic_formula.proof_parameters
           occurrence.Symbolic_state.formula))
    Substitution.String_set.empty
    (Symbolic_state.formulas state)

let is_truth_axiom state =
  List.exists
    (fun occurrence ->
      match occurrence.Symbolic_state.formula with
      | Symbolic_formula.Top -> true
      | _ -> false)
    (Symbolic_state.formulas state)

let atomic_closures state =
  let occurrences =
    Symbolic_state.formulas state
  in
  let rec pairs = function
    | [] ->
        []
    | occurrence :: rest ->
        let here =
          List.filter_map
            (fun other ->
              if
                Nested_sequent.compare_position
                  occurrence.Symbolic_state.position
                  other.Symbolic_state.position
                <> 0
              then
                None
              else
                match
                  occurrence.Symbolic_state.formula,
                  other.Symbolic_state.formula
                with
                | Symbolic_formula.PosAtom (left_name, left_arguments),
                  Symbolic_formula.NegAtom (right_name, right_arguments)
                  when String.equal left_name right_name
                       && List.length left_arguments
                          = List.length right_arguments ->
                    Some
                      {
                        positive_occurrence =
                          occurrence.Symbolic_state.occurrence_id;
                        negative_occurrence =
                          other.Symbolic_state.occurrence_id;
                        equations =
                          List.combine
                            left_arguments
                            right_arguments;
                      }

                | Symbolic_formula.NegAtom (left_name, left_arguments),
                  Symbolic_formula.PosAtom (right_name, right_arguments)
                  when String.equal left_name right_name
                       && List.length left_arguments
                          = List.length right_arguments ->
                    Some
                      {
                        positive_occurrence =
                          other.Symbolic_state.occurrence_id;
                        negative_occurrence =
                          occurrence.Symbolic_state.occurrence_id;
                        equations =
                          List.combine
                            left_arguments
                            right_arguments;
                      }

                | _ ->
                    None)
            rest
        in
        here @ pairs rest
  in
  pairs occurrences
let apply_or supply state occurrence_id =
  match Symbolic_state.find_occurrence state occurrence_id with
  | Some occurrence ->
      begin
        match occurrence.Symbolic_state.formula with
        | Symbolic_formula.Or (left, right) ->
            begin
              match
                Symbolic_state.remove_occurrence
                  state
                  occurrence_id
              with
              | None ->
                  None
              | Some state ->
                  begin
                    match
                      Symbolic_state.add_formula
                        supply
                        state
                        occurrence.Symbolic_state.position
                        left
                    with
                    | None ->
                        None
                    | Some
                        ( state,
                          left_occurrence,
                          supply ) ->
                        begin
                          match
                            Symbolic_state.add_formula
                              supply
                              state
                              occurrence.Symbolic_state.position
                              right
                          with
                          | None ->
                              None
                          | Some
                              ( state,
                                right_occurrence,
                                supply ) ->
                              Some
                                ( state,
                                  left_occurrence,
                                  right_occurrence,
                                  supply )
                        end
                  end
            end
        | _ ->
            None
      end
  | None ->
      None

let apply_and supply state occurrence_id =
  match Symbolic_state.find_occurrence state occurrence_id with
  | Some occurrence ->
      begin
        match occurrence.Symbolic_state.formula with
        | Symbolic_formula.And (left, right) ->
            begin
              match
                Symbolic_state.remove_occurrence
                  state
                  occurrence_id
              with
              | None ->
                  None
              | Some base_state ->
                  begin
                    match
                      Symbolic_state.add_formula
                        supply
                        base_state
                        occurrence.Symbolic_state.position
                        left
                    with
                    | None ->
                        None
                    | Some
                        ( left_state,
                          left_occurrence,
                          supply ) ->
                        begin
                          match
                            Symbolic_state.add_formula
                              supply
                              base_state
                              occurrence.Symbolic_state.position
                              right
                          with
                          | None ->
                              None
                          | Some
                              ( right_state,
                                right_occurrence,
                                supply ) ->
                              Some
                                ( left_state,
                                  left_occurrence,
                                  right_state,
                                  right_occurrence,
                                  supply )
                        end
                  end
            end
        | _ ->
            None
      end
  | None ->
      None

let apply_exists
    nested_supply
    symbolic_supply
    state
    occurrence_id
    ~active_eigenparameters
    ~birth_node =
  match Symbolic_state.find_occurrence state occurrence_id with
  | Some occurrence ->
      begin
        match occurrence.Symbolic_state.formula with
        | Symbolic_formula.Exists (variable, body) ->
            let meta, symbolic_supply =
              Symbolic_term.fresh_meta
                symbolic_supply
                ~active_eigenparameters
                ~birth_node
            in
            let instance =
              Symbolic_formula.substitute
                variable
                (Symbolic_term.Flex meta)
                body
            in
            begin
              match
                Symbolic_state.add_formula
                  nested_supply
                  state
                  occurrence.Symbolic_state.position
                  instance
              with
              | None ->
                  None
              | Some
                  ( state,
                    new_occurrence,
                    nested_supply ) ->
                  Some
                    ( state,
                      new_occurrence,
                      meta,
                      nested_supply,
                      symbolic_supply )
            end
        | _ ->
            None
      end
  | None ->
      None

let apply_forall
    supply
    state
    occurrence_id
    parameter =
  if
    Substitution.String_set.mem
      parameter
      (proof_parameters state)
  then
    None
  else
    match Symbolic_state.find_occurrence state occurrence_id with
    | Some occurrence ->
        begin
          match occurrence.Symbolic_state.formula with
          | Symbolic_formula.Forall (variable, body) ->
              let instance =
                Symbolic_formula.substitute
                  variable
                  (Symbolic_term.Param parameter)
                  body
              in
              begin
                match
                  Symbolic_state.remove_occurrence
                    state
                    occurrence_id
                with
                | None ->
                    None
                | Some state ->
                    Symbolic_state.add_formula
                      supply
                      state
                      occurrence.Symbolic_state.position
                      instance
              end
          | _ ->
              None
        end
    | None ->
        None

let apply_box supply state occurrence_id =
  match Symbolic_state.find_occurrence state occurrence_id with
  | Some occurrence ->
      begin
        match occurrence.Symbolic_state.formula with
        | Symbolic_formula.Box (modality, body) ->
            begin
              match
                Symbolic_state.remove_occurrence
                  state
                  occurrence_id
              with
              | None ->
                  None
              | Some state ->
                  begin
                    match
                      Symbolic_state.add_empty_child
                        supply
                        state
                        occurrence.Symbolic_state.position
                        modality
                    with
                    | None ->
                        None
                    | Some
                        ( state,
                          child_position,
                          supply ) ->
                        begin
                          match
                            Symbolic_state.add_formula
                              supply
                              state
                              child_position
                              body
                          with
                          | None ->
                              None
                          | Some
                              ( state,
                                new_occurrence,
                                supply ) ->
                              Some
                                ( state,
                                  child_position,
                                  new_occurrence,
                                  supply )
                        end
                  end
            end
        | _ ->
            None
      end
  | None ->
      None

let apply_diamond
    supply
    grammar
    state
    occurrence_id
    target
    certificate =
  match Symbolic_state.find_occurrence state occurrence_id with
  | Some occurrence ->
      begin
        match occurrence.Symbolic_state.formula with
        | Symbolic_formula.Diamond (modality, body) ->
            if
              Modal_certificate.valid
                ~grammar
                ~sequent:(Symbolic_state.tree state)
                ~modality
                ~source:occurrence.Symbolic_state.position
                ~target
                certificate
            then
              Symbolic_state.add_formula
                supply
                state
                target
                body
            else
              None
        | _ ->
            None
      end
  | None ->
      None

let apply_seriality
    supply
    axioms
    state
    parent
    modality =
  if
    not
      (Modal_axiom.Set.mem
         (Modal_axiom.D modality)
         axioms)
  then
    None
  else
    Symbolic_state.add_empty_child
      supply
      state
      parent
      modality
