type t = {
  answer : Answer_projection.answer;
  symbolic_derivation : Symbolic_derivation.t;
  ordinary_derivation : Derivation.t;
  substitution : Symbolic_substitution.t;
  residual_renaming : Proof_concretization.residual_renaming;
}

let renaming_contains renaming flexible =
  List.exists
    (fun (candidate, _) ->
      Symbolic_term.equal_flexible candidate flexible)
    renaming

let fresh_output_name used start =
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

let extend_renaming_for_answers
    ~avoid
    ~answer_representatives
    ~substitution
    renaming =
  let images =
    List.map
      (fun (_, representative) ->
        Symbolic_substitution.apply
          substitution
          (Symbolic_term.Flex representative))
      answer_representatives
  in
  let used =
    List.fold_left
      (fun used (_, name) ->
        Substitution.String_set.add name used)
      avoid
      renaming
  in
  let used =
    List.fold_left
      (fun used term ->
        let used =
          Substitution.String_set.union
            used
            (Symbolic_formula.ordinary_variables_term term)
        in
        Substitution.String_set.union
          used
          (Symbolic_term.proof_parameters term))
      used
      images
  in
  let residuals =
    List.concat_map
      Symbolic_term.flexible_variables
      images
    |> List.sort_uniq Symbolic_term.compare_flexible
  in
  let rec extend used next renaming = function
    | [] ->
        renaming
    | flexible :: rest ->
        if renaming_contains renaming flexible then
          extend used next renaming rest
        else
          let name, next =
            fresh_output_name used next
          in
          extend
            (Substitution.String_set.add name used)
            next
            ((flexible, name) :: renaming)
            rest
  in
  extend used 0 renaming residuals

let certify
    ~environment
    ~root
    (solved : Symbolic_search.solved_derivation) =
  let avoid =
    List.fold_left
      (fun names (variable, _) ->
        Substitution.String_set.add variable names)
      (Symbolic_search.names_to_avoid
         solved.Symbolic_search.derivation)
      (Symbolic_root.answer_representatives root)
  in
  match
    Proof_concretization.concretize
      ~avoid
      ~substitution:solved.Symbolic_search.substitution
      solved.Symbolic_search.derivation
  with
  | Error message ->
      Error message
  | Ok (residual_renaming, ordinary_derivation) ->
      let residual_renaming =
        extend_renaming_for_answers
          ~avoid
          ~answer_representatives:
            (Symbolic_root.answer_representatives root)
          ~substitution:
            solved.Symbolic_search.substitution
          residual_renaming
      in
      if
        not
          (Environment.check_derivation
             environment
             ordinary_derivation)
      then
        Error
          "reconstructed ordinary derivation failed certificate-kernel validation"
      else
        begin
          match
            Answer_projection.project_with_renaming
              ~answer_representatives:
                (Symbolic_root.answer_representatives root)
              ~substitution:
                solved.Symbolic_search.substitution
              ~renaming:residual_renaming
          with
          | Error message ->
              Error message
          | Ok answer ->
              Ok
                {
                  answer;
                  symbolic_derivation =
                    solved.Symbolic_search.derivation;
                  ordinary_derivation;
                  substitution =
                    solved.Symbolic_search.substitution;
                  residual_renaming;
                }
        end


let certify_without_global_eigenparameter_check =
  certify

let certify
    ~environment
    ~root
    (solved : Symbolic_search.solved_derivation) =
  if
    not
      (Symbolic_derivation.check_global_eigenparameters
         solved.Symbolic_search.derivation)
  then
    Error
      "symbolic derivation violates derivation-global eigenparameter freshness"
  else
    certify_without_global_eigenparameter_check
      ~environment
      ~root
      solved

let certify_without_symbolic_derivation_check =
  certify

let certify
    ~environment
    ~root
    (solved : Symbolic_search.solved_derivation) =
  if
    not
      (Symbolic_derivation.check
         ~environment
         solved.Symbolic_search.derivation)
  then
    Error
      "symbolic derivation failed generic validation"
  else
    certify_without_symbolic_derivation_check
      ~environment
      ~root
      solved

let certify_without_root_consistency_check =
  certify

let certify
    ~environment
    ~root
    (solved : Symbolic_search.solved_derivation) =
  if
    Symbolic_derivation.conclusion
      solved.Symbolic_search.derivation
    <> Symbolic_root.state root
  then
    Error
      "symbolic derivation root does not match the supplied symbolic root"
  else
    certify_without_root_consistency_check
      ~environment
      ~root
      solved
