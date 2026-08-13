type rule =
  | Truth_leaf
  | Atomic_leaf of Symbolic_kernel.atomic_closure
  | Or of Nested_sequent.occurrence_id
  | And of Nested_sequent.occurrence_id
  | Exists of
      Nested_sequent.occurrence_id
      * Symbolic_term.flexible_variable
  | Forall of
      Nested_sequent.occurrence_id
      * string
  | Box of
      Nested_sequent.occurrence_id
      * Nested_sequent.position
  | Diamond of
      Nested_sequent.occurrence_id
      * Nested_sequent.position
      * Modal_certificate.t
  | Seriality of
      Nested_sequent.position
      * Syntax.modal_index
      * Nested_sequent.position

type t = {
  node_id : int;
  conclusion : Symbolic_state.t;
  rule : rule;
  premises : t list;
}

let make ~node_id ~conclusion ~rule ~premises =
  {
    node_id;
    conclusion;
    rule;
    premises;
  }

let node_id derivation =
  derivation.node_id

let conclusion derivation =
  derivation.conclusion

let rule derivation =
  derivation.rule

let premises derivation =
  derivation.premises

let rec atomic_constraints derivation =
  let local =
    match derivation.rule with
    | Atomic_leaf closure ->
        closure.Symbolic_kernel.equations
    | _ ->
        []
  in
  local
  @ List.concat_map
      atomic_constraints
      derivation.premises

let rec height derivation =
  match derivation.premises with
  | [] ->
      0
  | premises ->
      1
      + List.fold_left
          max
          0
          (List.map height premises)

let check_global_eigenparameters derivation =
  let root_parameters =
    Symbolic_kernel.proof_parameters
      derivation.conclusion
  in
  let rec check seen derivation =
    let seen =
      match derivation.rule with
      | Forall (_, parameter) ->
          if
            Substitution.String_set.mem
              parameter
              root_parameters
            || Substitution.String_set.mem
                 parameter
                 seen
          then
            None
          else
            Some
              (Substitution.String_set.add
                 parameter
                 seen)
      | _ ->
          Some seen
    in
    match seen with
    | None ->
        None
    | Some seen ->
        List.fold_left
          (fun state premise ->
            match state with
            | None ->
                None
            | Some seen ->
                check seen premise)
          (Some seen)
          derivation.premises
  in
  match
    check
      Substitution.String_set.empty
      derivation
  with
  | None ->
      false
  | Some _ ->
      true

let same_occurrence_id left right =
  Nested_sequent.compare_occurrence_id left right = 0

let same_position left right =
  Nested_sequent.compare_position left right = 0

let occurrence_id_present state occurrence_id =
  Option.is_some
    (Symbolic_state.find_occurrence state occurrence_id)

let new_formula_occurrences ~before ~after =
  List.filter
    (fun occurrence ->
      not
        (occurrence_id_present
           before
           occurrence.Symbolic_state.occurrence_id))
    (Symbolic_state.formulas after)

let rec flexible_variables_formula = function
  | Symbolic_formula.PosAtom (_, terms)
  | Symbolic_formula.NegAtom (_, terms) ->
      List.concat_map
        Symbolic_term.flexible_variables
        terms

  | Symbolic_formula.Bottom
  | Symbolic_formula.Top ->
      []

  | Symbolic_formula.And (left, right)
  | Symbolic_formula.Or (left, right) ->
      flexible_variables_formula left
      @ flexible_variables_formula right

  | Symbolic_formula.Forall (_, body)
  | Symbolic_formula.Exists (_, body)
  | Symbolic_formula.Box (_, body)
  | Symbolic_formula.Diamond (_, body) ->
      flexible_variables_formula body

let flexible_variables_state state =
  List.concat_map
    (fun occurrence ->
      flexible_variables_formula
        occurrence.Symbolic_state.formula)
    (Symbolic_state.formulas state)

let flexible_present state flexible =
  List.exists
    (Symbolic_term.equal_flexible flexible)
    (flexible_variables_state state)

let symbolic_occurrence_ids_unique state =
  let rec loop seen = function
    | [] ->
        true
    | occurrence :: rest ->
        let occurrence_id =
          occurrence.Symbolic_state.occurrence_id
        in
        if
          List.exists
            (same_occurrence_id occurrence_id)
            seen
        then
          false
        else
          loop (occurrence_id :: seen) rest
  in
  loop [] (Symbolic_state.formulas state)

let valid_symbolic_state state =
  Nested_sequent.position_ids_unique
    (Symbolic_state.tree state)
  && symbolic_occurrence_ids_unique state
  && List.for_all
       (fun occurrence ->
         Symbolic_state.has_position
           state
           occurrence.Symbolic_state.position)
       (Symbolic_state.formulas state)

let atomic_closure_equal left right =
  same_occurrence_id
    left.Symbolic_kernel.positive_occurrence
    right.Symbolic_kernel.positive_occurrence
  && same_occurrence_id
       left.Symbolic_kernel.negative_occurrence
       right.Symbolic_kernel.negative_occurrence
  && left.Symbolic_kernel.equations
     = right.Symbolic_kernel.equations

let exactly_one_new_occurrence conclusion premise =
  match
    new_formula_occurrences
      ~before:conclusion
      ~after:premise
  with
  | [occurrence] ->
      Some occurrence
  | _ ->
      None

let check
    ~environment
    derivation =
  let grammar =
    Environment.grammar environment
  in
  let axioms =
    Environment.axioms environment
  in

  let rec check_node
      active_eigenparameters
      derivation =
    let conclusion =
      derivation.conclusion
    in

    if not (valid_symbolic_state conclusion) then
      false
    else
      match derivation.rule, derivation.premises with
      | Truth_leaf, [] ->
          Symbolic_kernel.is_truth_axiom conclusion

      | Atomic_leaf closure, [] ->
          List.exists
            (atomic_closure_equal closure)
            (Symbolic_kernel.atomic_closures conclusion)

      | Or occurrence_id, [premise] ->
          begin
            match
              Symbolic_state.find_occurrence
                conclusion
                occurrence_id
            with
            | Some occurrence ->
                begin
                  match occurrence.Symbolic_state.formula with
                  | Symbolic_formula.Or (left, right) ->
                      begin
                        match
                          Symbolic_state.remove_occurrence
                            conclusion
                            occurrence_id,
                          new_formula_occurrences
                            ~before:conclusion
                            ~after:premise.conclusion
                        with
                        | Some base, [first; second] ->
                            let reconstruct
                                first_formula
                                first_id
                                second_formula
                                second_id =
                              match
                                Symbolic_state.add_existing_formula
                                  base
                                  occurrence.Symbolic_state.position
                                  first_id
                                  first_formula
                              with
                              | None ->
                                  false
                              | Some state ->
                                  begin
                                    match
                                      Symbolic_state.add_existing_formula
                                        state
                                        occurrence.Symbolic_state.position
                                        second_id
                                        second_formula
                                    with
                                    | None ->
                                        false
                                    | Some state ->
                                        Symbolic_state.equal
                                          state
                                          premise.conclusion
                                  end
                            in
                            let first_id =
                              first.Symbolic_state.occurrence_id
                            in
                            let second_id =
                              second.Symbolic_state.occurrence_id
                            in
                            (reconstruct
                               left
                               first_id
                               right
                               second_id
                             || reconstruct
                                  left
                                  second_id
                                  right
                                  first_id)
                            && check_node
                                 active_eigenparameters
                                 premise

                        | _ ->
                            false
                      end

                  | _ ->
                      false
                end

            | None ->
                false
          end

      | And occurrence_id, [left_premise; right_premise] ->
          begin
            match
              Symbolic_state.find_occurrence
                conclusion
                occurrence_id
            with
            | Some occurrence ->
                begin
                  match occurrence.Symbolic_state.formula with
                  | Symbolic_formula.And (left, right) ->
                      begin
                        match
                          Symbolic_state.remove_occurrence
                            conclusion
                            occurrence_id,
                          exactly_one_new_occurrence
                            conclusion
                            left_premise.conclusion,
                          exactly_one_new_occurrence
                            conclusion
                            right_premise.conclusion
                        with
                        | Some base,
                          Some left_new,
                          Some right_new ->
                            let left_state =
                              Symbolic_state.add_existing_formula
                                base
                                occurrence.Symbolic_state.position
                                left_new.Symbolic_state.occurrence_id
                                left
                            in
                            let right_state =
                              Symbolic_state.add_existing_formula
                                base
                                occurrence.Symbolic_state.position
                                right_new.Symbolic_state.occurrence_id
                                right
                            in
                            begin
                              match left_state, right_state with
                              | Some left_state,
                                Some right_state ->
                                  Symbolic_state.equal
                                    left_state
                                    left_premise.conclusion
                                  && Symbolic_state.equal
                                       right_state
                                       right_premise.conclusion
                                  && check_node
                                       active_eigenparameters
                                       left_premise
                                  && check_node
                                       active_eigenparameters
                                       right_premise
                              | _ ->
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

      | Exists (occurrence_id, witness), [premise] ->
          begin
            match
              Symbolic_state.find_occurrence
                conclusion
                occurrence_id
            with
            | Some occurrence ->
                begin
                  match occurrence.Symbolic_state.formula with
                  | Symbolic_formula.Exists (variable, body) ->
                      begin
                        match
                          exactly_one_new_occurrence
                            conclusion
                            premise.conclusion
                        with
                        | None ->
                            false
                        | Some new_occurrence ->
                            let instance =
                              Symbolic_formula.substitute
                                variable
                                (Symbolic_term.Flex witness)
                                body
                            in
                            begin
                              match
                                Symbolic_state.add_existing_formula
                                  conclusion
                                  occurrence.Symbolic_state.position
                                  new_occurrence.Symbolic_state.occurrence_id
                                  instance
                              with
                              | None ->
                                  false
                              | Some expected ->
                                  Symbolic_term.kind witness
                                    = Symbolic_term.Witness
                                  && not
                                       (flexible_present
                                          conclusion
                                          witness)
                                  && Substitution.String_set.equal
                                       (Symbolic_term.permission witness)
                                       active_eigenparameters
                                  && Symbolic_term.birth_node witness
                                     = Some derivation.node_id
                                  && Symbolic_state.equal
                                       expected
                                       premise.conclusion
                                  && check_node
                                       active_eigenparameters
                                       premise
                            end
                      end

                  | _ ->
                      false
                end

            | None ->
                false
          end

      | Forall (occurrence_id, parameter), [premise] ->
          begin
            match
              Symbolic_state.find_occurrence
                conclusion
                occurrence_id
            with
            | Some occurrence ->
                begin
                  match occurrence.Symbolic_state.formula with
                  | Symbolic_formula.Forall (variable, body) ->
                      if
                        Substitution.String_set.mem
                          parameter
                          (Symbolic_kernel.proof_parameters
                             conclusion)
                      then
                        false
                      else
                        begin
                          match
                            Symbolic_state.remove_occurrence
                              conclusion
                              occurrence_id,
                            exactly_one_new_occurrence
                              conclusion
                              premise.conclusion
                          with
                          | Some base, Some new_occurrence ->
                              let instance =
                                Symbolic_formula.substitute
                                  variable
                                  (Symbolic_term.Param parameter)
                                  body
                              in
                              begin
                                match
                                  Symbolic_state.add_existing_formula
                                    base
                                    occurrence.Symbolic_state.position
                                    new_occurrence.Symbolic_state.occurrence_id
                                    instance
                                with
                                | None ->
                                    false
                                | Some expected ->
                                    Symbolic_state.equal
                                      expected
                                      premise.conclusion
                                    && check_node
                                         (Substitution.String_set.add
                                            parameter
                                            active_eigenparameters)
                                         premise
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

      | Box (occurrence_id, child_position), [premise] ->
          begin
            match
              Symbolic_state.find_occurrence
                conclusion
                occurrence_id
            with
            | Some occurrence ->
                begin
                  match occurrence.Symbolic_state.formula with
                  | Symbolic_formula.Box (modality, body) ->
                      begin
                        match
                          Symbolic_state.remove_occurrence
                            conclusion
                            occurrence_id,
                          exactly_one_new_occurrence
                            conclusion
                            premise.conclusion
                        with
                        | Some base, Some new_occurrence ->
                            begin
                              match
                                Symbolic_state.add_existing_empty_child
                                  base
                                  occurrence.Symbolic_state.position
                                  modality
                                  child_position
                              with
                              | None ->
                                  false
                              | Some state ->
                                  begin
                                    match
                                      Symbolic_state.add_existing_formula
                                        state
                                        child_position
                                        new_occurrence.Symbolic_state.occurrence_id
                                        body
                                    with
                                    | None ->
                                        false
                                    | Some expected ->
                                        Symbolic_state.equal
                                          expected
                                          premise.conclusion
                                        && check_node
                                             active_eigenparameters
                                             premise
                                  end
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

      | Diamond
          (occurrence_id, target, certificate),
        [premise] ->
          begin
            match
              Symbolic_state.find_occurrence
                conclusion
                occurrence_id
            with
            | Some occurrence ->
                begin
                  match occurrence.Symbolic_state.formula with
                  | Symbolic_formula.Diamond (modality, body) ->
                      if
                        not
                          (Modal_certificate.valid
                             ~grammar
                             ~sequent:
                               (Symbolic_state.tree conclusion)
                             ~modality
                             ~source:
                               occurrence.Symbolic_state.position
                             ~target
                             certificate)
                      then
                        false
                      else
                        begin
                          match
                            exactly_one_new_occurrence
                              conclusion
                              premise.conclusion
                          with
                          | None ->
                              false
                          | Some new_occurrence ->
                              begin
                                match
                                  Symbolic_state.add_existing_formula
                                    conclusion
                                    target
                                    new_occurrence.Symbolic_state.occurrence_id
                                    body
                                with
                                | None ->
                                    false
                                | Some expected ->
                                    Symbolic_state.equal
                                      expected
                                      premise.conclusion
                                    && check_node
                                         active_eigenparameters
                                         premise
                              end
                        end

                  | _ ->
                      false
                end

            | None ->
                false
          end

      | Seriality
          (parent, modality, child_position),
        [premise] ->
          if
            not
              (Modal_axiom.Set.mem
                 (Modal_axiom.D modality)
                 axioms)
          then
            false
          else
            begin
              match
                Symbolic_state.add_existing_empty_child
                  conclusion
                  parent
                  modality
                  child_position
              with
              | None ->
                  false
              | Some expected ->
                  Symbolic_state.equal
                    expected
                    premise.conclusion
                  && check_node
                       active_eigenparameters
                       premise
            end

      | _ ->
          false
  in

  check_global_eigenparameters derivation
  && check_node
       Substitution.String_set.empty
       derivation
