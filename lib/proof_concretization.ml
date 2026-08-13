type residual_renaming =
  (Symbolic_term.flexible_variable * string) list

let rec terms_of_formula = function
  | Symbolic_formula.PosAtom (_, terms)
  | Symbolic_formula.NegAtom (_, terms) ->
      terms
  | Symbolic_formula.Bottom
  | Symbolic_formula.Top ->
      []
  | Symbolic_formula.And (left, right)
  | Symbolic_formula.Or (left, right) ->
      terms_of_formula left @ terms_of_formula right
  | Symbolic_formula.Forall (_, body)
  | Symbolic_formula.Exists (_, body)
  | Symbolic_formula.Box (_, body)
  | Symbolic_formula.Diamond (_, body) ->
      terms_of_formula body

let residuals_of_term substitution term =
  Symbolic_substitution.apply substitution term
  |> Symbolic_term.flexible_variables

let residuals_of_formula substitution formula =
  terms_of_formula formula
  |> List.concat_map (residuals_of_term substitution)

let add_term_names substitution used term =
  let term =
    Symbolic_substitution.apply substitution term
  in
  let used =
    Substitution.String_set.union
      used
      (Symbolic_formula.ordinary_variables_term term)
  in
  Substitution.String_set.union
    used
    (Symbolic_term.proof_parameters term)

let add_formula_names substitution used formula =
  let formula =
    Symbolic_formula.apply_substitution substitution formula
  in
  let used =
    Substitution.String_set.union
      used
      (Symbolic_formula.ordinary_variables formula)
  in
  Substitution.String_set.union
    used
    (Symbolic_formula.proof_parameters formula)

let fresh_name used start =
  let rec choose index =
    let candidate =
      "Y" ^ string_of_int index
    in
    if Substitution.String_set.mem candidate used then
      choose (index + 1)
    else
      candidate, index + 1
  in
  choose start

let build_residual_renaming
    ~avoid
    ~substitution
    derivation =
  let rec collect derivation (used, residuals) =
    let state =
      Symbolic_derivation.conclusion derivation
    in
    let used, residuals =
      List.fold_left
        (fun (used, residuals) occurrence ->
          let formula =
            occurrence.Symbolic_state.formula
          in
          ( add_formula_names substitution used formula,
            residuals_of_formula substitution formula @ residuals ))
        (used, residuals)
        (Symbolic_state.formulas state)
    in
    let used, residuals =
      match Symbolic_derivation.rule derivation with
      | Symbolic_derivation.Exists (_, flexible) ->
          let term =
            Symbolic_term.Flex flexible
          in
          ( add_term_names substitution used term,
            residuals_of_term substitution term @ residuals )
      | _ ->
          used, residuals
    in
    List.fold_left
      (fun accumulator premise ->
        collect premise accumulator)
      (used, residuals)
      (Symbolic_derivation.premises derivation)
  in
  let used, residuals =
    collect derivation (avoid, [])
  in
  let residuals =
    List.sort_uniq
      Symbolic_term.compare_flexible
      residuals
  in
  let rec assign used next renaming = function
    | [] ->
        List.rev renaming
    | flexible :: rest ->
        let name, next =
          fresh_name used next
        in
        assign
          (Substitution.String_set.add name used)
          next
          ((flexible, name) :: renaming)
          rest
  in
  assign used 0 [] residuals

let lookup_residual renaming flexible =
  List.find_opt
    (fun (candidate, _) ->
      Symbolic_term.equal_flexible
        candidate
        flexible)
    renaming

let rec concretize_applied_term renaming = function
  | Symbolic_term.Var variable ->
      Ok (Syntax.Var variable)
  | Symbolic_term.Param parameter ->
      Ok (Syntax.Param parameter)
  | Symbolic_term.Const constant ->
      Ok (Syntax.Const constant)
  | Symbolic_term.Flex flexible ->
      begin
        match lookup_residual renaming flexible with
        | Some (_, variable) ->
            Ok (Syntax.Var variable)
        | None ->
            Error
              "proof concretization encountered an unregistered residual flexible variable"
      end
  | Symbolic_term.Fun (name, arguments) ->
      let rec convert converted = function
        | [] ->
            Ok
              (Syntax.Fun
                 (name, List.rev converted))
        | argument :: rest ->
            begin
              match concretize_applied_term renaming argument with
              | Error message ->
                  Error message
              | Ok argument ->
                  convert
                    (argument :: converted)
                    rest
            end
      in
      convert [] arguments

let concretize_term
    ~substitution
    ~renaming
    term =
  concretize_applied_term
    renaming
    (Symbolic_substitution.apply substitution term)

let rec concretize_formula
    ~substitution
    ~renaming
    formula =
  let convert_terms terms =
    let rec loop converted = function
      | [] ->
          Ok (List.rev converted)
      | term :: rest ->
          begin
            match
              concretize_term
                ~substitution
                ~renaming
                term
            with
            | Error message ->
                Error message
            | Ok term ->
                loop (term :: converted) rest
          end
    in
    loop [] terms
  in
  let convert_binary constructor left right =
    match
      concretize_formula
        ~substitution
        ~renaming
        left
    with
    | Error message ->
        Error message
    | Ok left ->
        begin
          match
            concretize_formula
              ~substitution
              ~renaming
              right
          with
          | Error message ->
              Error message
          | Ok right ->
              Ok (constructor left right)
        end
  in
  match formula with
  | Symbolic_formula.PosAtom (predicate, terms) ->
      begin
        match convert_terms terms with
        | Error message ->
            Error message
        | Ok terms ->
            Ok (Syntax.PosAtom (predicate, terms))
      end
  | Symbolic_formula.NegAtom (predicate, terms) ->
      begin
        match convert_terms terms with
        | Error message ->
            Error message
        | Ok terms ->
            Ok (Syntax.NegAtom (predicate, terms))
      end
  | Symbolic_formula.Bottom ->
      Ok Syntax.CoreBottom
  | Symbolic_formula.Top ->
      Ok Syntax.CoreTop
  | Symbolic_formula.And (left, right) ->
      convert_binary
        (fun left right ->
          Syntax.CoreAnd (left, right))
        left
        right
  | Symbolic_formula.Or (left, right) ->
      convert_binary
        (fun left right ->
          Syntax.CoreOr (left, right))
        left
        right
  | Symbolic_formula.Forall (variable, body) ->
      begin
        match
          concretize_formula
            ~substitution
            ~renaming
            body
        with
        | Error message ->
            Error message
        | Ok body ->
            Ok (Syntax.CoreForall (variable, body))
      end
  | Symbolic_formula.Exists (variable, body) ->
      begin
        match
          concretize_formula
            ~substitution
            ~renaming
            body
        with
        | Error message ->
            Error message
        | Ok body ->
            Ok (Syntax.CoreExists (variable, body))
      end
  | Symbolic_formula.Box (modality, body) ->
      begin
        match
          concretize_formula
            ~substitution
            ~renaming
            body
        with
        | Error message ->
            Error message
        | Ok body ->
            Ok (Syntax.CoreBox (modality, body))
      end
  | Symbolic_formula.Diamond (modality, body) ->
      begin
        match
          concretize_formula
            ~substitution
            ~renaming
            body
        with
        | Error message ->
            Error message
        | Ok body ->
            Ok (Syntax.CoreDiamond (modality, body))
      end

let concretize_state
    ~substitution
    ~renaming
    state =
  let rec add_occurrences sequent = function
    | [] ->
        Ok sequent
    | occurrence :: rest ->
        begin
          match
            concretize_formula
              ~substitution
              ~renaming
              occurrence.Symbolic_state.formula
          with
          | Error message ->
              Error message
          | Ok formula ->
              let ordinary_occurrence :
                  Nested_sequent.formula_occurrence =
                {
                  occurrence_id =
                    occurrence.Symbolic_state.occurrence_id;
                  formula;
                }
              in
              begin
                match
                  Nested_sequent.add_existing_occurrence
                    sequent
                    occurrence.Symbolic_state.position
                    ordinary_occurrence
                with
                | None ->
                    Error
                      "proof concretization failed to preserve a symbolic occurrence"
                | Some sequent ->
                    add_occurrences sequent rest
              end
        end
  in
  add_occurrences
    (Symbolic_state.tree state)
    (Symbolic_state.formulas state)

let concretize_rule
    ~substitution
    ~renaming
    rule =
  match rule with
  | Symbolic_derivation.Truth_leaf ->
      Ok Derivation.Truth_axiom
  | Symbolic_derivation.Atomic_leaf _ ->
      Ok Derivation.Atomic_axiom
  | Symbolic_derivation.Or occurrence_id ->
      Ok (Derivation.Or occurrence_id)
  | Symbolic_derivation.And occurrence_id ->
      Ok (Derivation.And occurrence_id)
  | Symbolic_derivation.Exists (occurrence_id, flexible) ->
      begin
        match
          concretize_term
            ~substitution
            ~renaming
            (Symbolic_term.Flex flexible)
        with
        | Error message ->
            Error message
        | Ok witness ->
            Ok
              (Derivation.Exists
                 (occurrence_id, witness))
      end
  | Symbolic_derivation.Forall (occurrence_id, parameter) ->
      Ok
        (Derivation.Forall
           (occurrence_id, parameter))
  | Symbolic_derivation.Box (occurrence_id, position) ->
      Ok
        (Derivation.Box
           (occurrence_id, position))
  | Symbolic_derivation.Diamond
      (occurrence_id, position, certificate) ->
      Ok
        (Derivation.Diamond
           (occurrence_id, position, certificate))
  | Symbolic_derivation.Seriality
      (position, modality, child_position) ->
      Ok
        (Derivation.Seriality
           (position, modality, child_position))

let rec concretize_derivation
    ~substitution
    ~renaming
    derivation =
  match
    concretize_state
      ~substitution
      ~renaming
      (Symbolic_derivation.conclusion derivation)
  with
  | Error message ->
      Error message
  | Ok conclusion ->
      begin
        match
          concretize_rule
            ~substitution
            ~renaming
            (Symbolic_derivation.rule derivation)
        with
        | Error message ->
            Error message
        | Ok rule ->
            let rec convert_premises converted = function
              | [] ->
                  Ok (List.rev converted)
              | premise :: rest ->
                  begin
                    match
                      concretize_derivation
                        ~substitution
                        ~renaming
                        premise
                    with
                    | Error message ->
                        Error message
                    | Ok premise ->
                        convert_premises
                          (premise :: converted)
                          rest
                  end
            in
            begin
              match
                convert_premises
                  []
                  (Symbolic_derivation.premises derivation)
              with
              | Error message ->
                  Error message
              | Ok premises ->
                  Ok
                    {
                      Derivation.conclusion;
                      rule;
                      premises;
                    }
            end
      end

let concretize
    ~avoid
    ~substitution
    derivation =
  let renaming =
    build_residual_renaming
      ~avoid
      ~substitution
      derivation
  in
  match
    concretize_derivation
      ~substitution
      ~renaming
      derivation
  with
  | Error message ->
      Error message
  | Ok derivation ->
      Ok (renaming, derivation)
