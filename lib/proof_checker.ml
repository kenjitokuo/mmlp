let valid_state sequent =
  Nested_sequent.position_ids_unique sequent
  && Nested_sequent.occurrence_ids_unique sequent

let check_axiom_node node =
  valid_state node.Derivation.conclusion
  &&
  match node.Derivation.rule, node.Derivation.premises with
  | Derivation.Truth_axiom, [] ->
      Kernel.is_truth_axiom node.Derivation.conclusion
  | Derivation.Atomic_axiom, [] ->
      Kernel.is_atomic_axiom node.Derivation.conclusion
  | _ ->
      false

let check_or_node node occurrence_id =
  match node.Derivation.premises with
  | [premise] ->
      let conclusion = node.Derivation.conclusion in
      let premise_state = premise.Derivation.conclusion in
      if not (valid_state conclusion && valid_state premise_state) then
        false
      else
        begin
          match Nested_sequent.find_occurrence conclusion occurrence_id with
          | None ->
              false
          | Some (position, principal) ->
              begin
                match principal.Nested_sequent.formula with
                | Syntax.CoreOr (a, b) ->
                    let new_ids =
                      Nested_sequent.new_occurrence_ids
                        ~before:conclusion
                        ~after:premise_state
                    in
                    begin
                      match new_ids with
                      | [id1; id2] ->
                          begin
                            match
                              Nested_sequent.find_occurrence premise_state id1,
                              Nested_sequent.find_occurrence premise_state id2
                            with
                            | Some (p1, o1), Some (p2, o2) ->
                                let same_position =
                                  Nested_sequent.compare_position p1 position = 0
                                  && Nested_sequent.compare_position p2 position = 0
                                in
                                let formulas_match =
                                  (o1.Nested_sequent.formula = a
                                   && o2.Nested_sequent.formula = b)
                                  ||
                                  (o1.Nested_sequent.formula = b
                                   && o2.Nested_sequent.formula = a)
                                in
                                if not (same_position && formulas_match) then
                                  false
                                else
                                  begin
                                    match
                                      Nested_sequent.remove_occurrence
                                        conclusion
                                        occurrence_id
                                    with
                                    | None ->
                                        false
                                    | Some base ->
                                        begin
                                          match
                                            Nested_sequent.add_existing_occurrence
                                              base
                                              position
                                              o1
                                          with
                                          | None ->
                                              false
                                          | Some expected1 ->
                                              begin
                                                match
                                                  Nested_sequent.add_existing_occurrence
                                                    expected1
                                                    position
                                                    o2
                                                with
                                                | None ->
                                                    false
                                                | Some expected2 ->
                                                    Nested_sequent.equal
                                                      expected2
                                                      premise_state
                                              end
                                        end
                                  end
                            | _ ->
                                false
                          end
                      | _ ->
                          false
                    end
                | _ ->
                    false
              end
        end
  | _ ->
      false

let check_and_premise conclusion position occurrence_id expected_formula premise_state =
  if not (valid_state premise_state) then
    false
  else
    let new_ids =
      Nested_sequent.new_occurrence_ids
        ~before:conclusion
        ~after:premise_state
    in
    match new_ids with
    | [new_id] ->
        begin
          match Nested_sequent.find_occurrence premise_state new_id with
          | Some (new_position, new_occurrence) ->
              if
                Nested_sequent.compare_position new_position position <> 0
                || new_occurrence.Nested_sequent.formula <> expected_formula
              then
                false
              else
                begin
                  match
                    Nested_sequent.remove_occurrence
                      conclusion
                      occurrence_id
                  with
                  | None ->
                      false
                  | Some base ->
                      begin
                        match
                          Nested_sequent.add_existing_occurrence
                            base
                            position
                            new_occurrence
                        with
                        | None ->
                            false
                        | Some expected ->
                            Nested_sequent.equal expected premise_state
                      end
                end
          | None ->
              false
        end
    | _ ->
        false

let check_and_node node occurrence_id =
  match node.Derivation.premises with
  | [premise1; premise2] ->
      let conclusion = node.Derivation.conclusion in
      if not (valid_state conclusion) then
        false
      else
        begin
          match Nested_sequent.find_occurrence conclusion occurrence_id with
          | Some (position, principal) ->
              begin
                match principal.Nested_sequent.formula with
                | Syntax.CoreAnd (a, b) ->
                    let state1 = premise1.Derivation.conclusion in
                    let state2 = premise2.Derivation.conclusion in
                    (check_and_premise
                       conclusion
                       position
                       occurrence_id
                       a
                       state1
                     &&
                     check_and_premise
                       conclusion
                       position
                       occurrence_id
                       b
                       state2)
                    ||
                    (check_and_premise
                       conclusion
                       position
                       occurrence_id
                       b
                       state1
                     &&
                     check_and_premise
                       conclusion
                       position
                       occurrence_id
                       a
                       state2)
                | _ ->
                    false
              end
          | None ->
              false
        end
  | _ ->
      false

let check_exists_node node occurrence_id witness =
  match node.Derivation.premises with
  | [premise] ->
      let conclusion = node.Derivation.conclusion in
      let premise_state = premise.Derivation.conclusion in
      if not (valid_state conclusion && valid_state premise_state) then
        false
      else
        begin
          match Nested_sequent.find_occurrence conclusion occurrence_id with
          | Some (position, principal) ->
              begin
                match principal.Nested_sequent.formula with
                | Syntax.CoreExists (variable, body) ->
                    let expected_formula =
                      Substitution.core_formula
                        ~variable
                        ~replacement:witness
                        body
                    in
                    let new_ids =
                      Nested_sequent.new_occurrence_ids
                        ~before:conclusion
                        ~after:premise_state
                    in
                    begin
                      match new_ids with
                      | [new_id] ->
                          begin
                            match
                              Nested_sequent.find_occurrence
                                premise_state
                                new_id
                            with
                            | Some (new_position, new_occurrence) ->
                                if
                                  Nested_sequent.compare_position
                                    new_position
                                    position
                                  <> 0
                                  ||
                                  new_occurrence.Nested_sequent.formula
                                  <> expected_formula
                                then
                                  false
                                else
                                  begin
                                    match
                                      Nested_sequent.add_existing_occurrence
                                        conclusion
                                        position
                                        new_occurrence
                                    with
                                    | None ->
                                        false
                                    | Some expected ->
                                        Nested_sequent.equal
                                          expected
                                          premise_state
                                  end
                            | None ->
                                false
                          end
                      | _ ->
                          false
                    end
                | _ ->
                    false
              end
          | None ->
              false
        end
  | _ ->
      false

let check_forall_node node occurrence_id parameter =
  match node.Derivation.premises with
  | [premise] ->
      let conclusion = node.Derivation.conclusion in
      let premise_state = premise.Derivation.conclusion in
      if not (valid_state conclusion && valid_state premise_state) then
        false
      else if
        Substitution.String_set.mem
          parameter
          (Nested_sequent.proof_params conclusion)
      then
        false
      else
        begin
          match Nested_sequent.find_occurrence conclusion occurrence_id with
          | Some (position, principal) ->
              begin
                match principal.Nested_sequent.formula with
                | Syntax.CoreForall (variable, body) ->
                    let expected_formula =
                      Substitution.core_formula
                        ~variable
                        ~replacement:(Syntax.Param parameter)
                        body
                    in
                    let new_ids =
                      Nested_sequent.new_occurrence_ids
                        ~before:conclusion
                        ~after:premise_state
                    in
                    begin
                      match new_ids with
                      | [new_id] ->
                          begin
                            match
                              Nested_sequent.find_occurrence
                                premise_state
                                new_id
                            with
                            | Some (new_position, new_occurrence) ->
                                if
                                  Nested_sequent.compare_position
                                    new_position
                                    position
                                  <> 0
                                  ||
                                  new_occurrence.Nested_sequent.formula
                                  <> expected_formula
                                then
                                  false
                                else
                                  begin
                                    match
                                      Nested_sequent.remove_occurrence
                                        conclusion
                                        occurrence_id
                                    with
                                    | None ->
                                        false
                                    | Some base ->
                                        begin
                                          match
                                            Nested_sequent.add_existing_occurrence
                                              base
                                              position
                                              new_occurrence
                                          with
                                          | None ->
                                              false
                                          | Some expected ->
                                              Nested_sequent.equal
                                                expected
                                                premise_state
                                        end
                                  end
                            | None ->
                                false
                          end
                      | _ ->
                          false
                    end
                | _ ->
                    false
              end
          | None ->
              false
        end
  | _ ->
      false

let check_box_node node occurrence_id child_position =
  match node.Derivation.premises with
  | [premise] ->
      let conclusion = node.Derivation.conclusion in
      let premise_state = premise.Derivation.conclusion in
      if not (valid_state conclusion && valid_state premise_state) then
        false
      else
        begin
          match Nested_sequent.find_occurrence conclusion occurrence_id with
          | Some (parent_position, principal) ->
              begin
                match principal.Nested_sequent.formula with
                | Syntax.CoreBox (modality, body) ->
                    let new_ids =
                      Nested_sequent.new_occurrence_ids
                        ~before:conclusion
                        ~after:premise_state
                    in
                    begin
                      match new_ids with
                      | [new_id] ->
                          begin
                            match
                              Nested_sequent.find_occurrence
                                premise_state
                                new_id
                            with
                            | Some (body_position, body_occurrence) ->
                                if
                                  Nested_sequent.compare_position
                                    body_position
                                    child_position
                                  <> 0
                                  ||
                                  body_occurrence.Nested_sequent.formula
                                  <> body
                                then
                                  false
                                else
                                  begin
                                    match
                                      Nested_sequent.remove_occurrence
                                        conclusion
                                        occurrence_id
                                    with
                                    | None ->
                                        false
                                    | Some base ->
                                        begin
                                          match
                                            Nested_sequent.add_existing_empty_child
                                              base
                                              parent_position
                                              modality
                                              child_position
                                          with
                                          | None ->
                                              false
                                          | Some with_child ->
                                              begin
                                                match
                                                  Nested_sequent.add_existing_occurrence
                                                    with_child
                                                    child_position
                                                    body_occurrence
                                                with
                                                | None ->
                                                    false
                                                | Some expected ->
                                                    Nested_sequent.equal
                                                      expected
                                                      premise_state
                                              end
                                        end
                                  end
                            | None ->
                                false
                          end
                      | _ ->
                          false
                    end
                | _ ->
                    false
              end
          | None ->
              false
        end
  | _ ->
      false

let check_diamond_node ~grammar node occurrence_id target certificate =
  match node.Derivation.premises with
  | [premise] ->
      let conclusion = node.Derivation.conclusion in
      let premise_state = premise.Derivation.conclusion in
      if not (valid_state conclusion && valid_state premise_state) then
        false
      else
        begin
          match Nested_sequent.find_occurrence conclusion occurrence_id with
          | Some (source, principal) ->
              begin
                match principal.Nested_sequent.formula with
                | Syntax.CoreDiamond (modality, body) ->
                    if not (Nested_sequent.has_position conclusion target) then
                      false
                    else if
                      not
                        (Modal_certificate.valid
                           ~grammar
                           ~sequent:conclusion
                           ~modality
                           ~source
                           ~target
                           certificate)
                    then
                      false
                    else
                      let new_ids =
                        Nested_sequent.new_occurrence_ids
                          ~before:conclusion
                          ~after:premise_state
                      in
                      begin
                        match new_ids with
                        | [new_id] ->
                            begin
                              match
                                Nested_sequent.find_occurrence
                                  premise_state
                                  new_id
                              with
                              | Some (body_position, body_occurrence) ->
                                  if
                                    Nested_sequent.compare_position
                                      body_position
                                      target
                                    <> 0
                                    ||
                                    body_occurrence.Nested_sequent.formula
                                    <> body
                                  then
                                    false
                                  else
                                    begin
                                      match
                                        Nested_sequent.add_existing_occurrence
                                          conclusion
                                          target
                                          body_occurrence
                                      with
                                      | None ->
                                          false
                                      | Some expected ->
                                          Nested_sequent.equal
                                            expected
                                            premise_state
                                    end
                              | None ->
                                  false
                            end
                        | _ ->
                            false
                      end
                | _ ->
                    false
              end
          | None ->
              false
        end
  | _ ->
      false

let check_seriality_node ~axioms node parent_position modality child_position =
  match node.Derivation.premises with
  | [premise] ->
      let conclusion = node.Derivation.conclusion in
      let premise_state = premise.Derivation.conclusion in
      if not (valid_state conclusion && valid_state premise_state) then
        false
      else if
        not (Modal_axiom.Set.mem (Modal_axiom.D modality) axioms)
      then
        false
      else if not (Nested_sequent.has_position conclusion parent_position) then
        false
      else
        begin
          match
            Nested_sequent.new_position_ids
              ~before:conclusion
              ~after:premise_state
          with
          | [new_position]
              when Nested_sequent.compare_position
                     new_position
                     child_position = 0 ->
              if
                Nested_sequent.new_occurrence_ids
                  ~before:conclusion
                  ~after:premise_state
                <> []
              then
                false
              else
                begin
                  match
                    Nested_sequent.add_existing_empty_child
                      conclusion
                      parent_position
                      modality
                      child_position
                  with
                  | None ->
                      false
                  | Some expected ->
                      Nested_sequent.equal expected premise_state
                end
          | _ ->
              false
        end
  | _ ->
      false

let rec signature_valid_state ~signature sequent =
  List.for_all
    (fun occurrence ->
      match
        Signature.validate_core_formula
          signature
          occurrence.Nested_sequent.formula
      with
      | Ok () -> true
      | Error _ -> false)
    sequent.Nested_sequent.formulas
  &&
  List.for_all
    (fun child ->
      signature_valid_state
        ~signature
        child.Nested_sequent.subtree)
    sequent.Nested_sequent.children

let valid ~signature ~axioms derivation =
  let grammar = Grammar.of_axioms axioms in
  let rec check node =
    let signature_valid =
      signature_valid_state
        ~signature
        node.Derivation.conclusion
    in
    let local_valid =
      signature_valid
      &&
      match node.Derivation.rule with
      | Derivation.Truth_axiom
      | Derivation.Atomic_axiom ->
          check_axiom_node node
      | Derivation.Or occurrence_id ->
          check_or_node node occurrence_id
      | Derivation.And occurrence_id ->
          check_and_node node occurrence_id
      | Derivation.Exists (occurrence_id, witness) ->
          begin
            match Signature.validate_term signature witness with
            | Error _ -> false
            | Ok () ->
                check_exists_node node occurrence_id witness
          end
      | Derivation.Forall (occurrence_id, parameter) ->
          check_forall_node node occurrence_id parameter
      | Derivation.Box (occurrence_id, child_position) ->
          check_box_node node occurrence_id child_position
      | Derivation.Diamond (occurrence_id, target, certificate) ->
          check_diamond_node
            ~grammar
            node
            occurrence_id
            target
            certificate
      | Derivation.Seriality
          (parent_position, modality, child_position) ->
          check_seriality_node
            ~axioms
            node
            parent_position
            modality
            child_position
    in
    local_valid
    && List.for_all check node.Derivation.premises
  in
  check derivation
