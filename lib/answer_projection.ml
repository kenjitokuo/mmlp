type answer =
  (string * Syntax.term) list

let rec ordinary_variables = function
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
            (ordinary_variables argument))
        Substitution.String_set.empty
        arguments

let residuals term =
  Symbolic_term.flexible_variables term
  |> List.sort_uniq Symbolic_term.compare_flexible

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

let build_residual_renaming ~avoid images =
  let used =
    List.fold_left
      (fun variables (_, term) ->
        Substitution.String_set.union
          variables
          (ordinary_variables term))
      avoid
      images
  in
  let all_residuals =
    List.concat_map
      (fun (_, term) -> residuals term)
      images
    |> List.sort_uniq Symbolic_term.compare_flexible
  in
  let rec assign used next renaming = function
    | [] ->
        Ok renaming
    | flexible :: rest ->
        if
          not
            (Substitution.String_set.is_empty
               (Symbolic_term.permission flexible))
        then
          Error
            "answer contains a residual flexible variable with nonempty permission"
        else
          let name, next =
            fresh_output_name used next
          in
          assign
            (Substitution.String_set.add name used)
            next
            ((flexible, name) :: renaming)
            rest
  in
  assign used 0 [] all_residuals

let rec concretize renaming = function
  | Symbolic_term.Var variable ->
      Ok (Syntax.Var variable)
  | Symbolic_term.Param _ ->
      Error "answer contains a proof eigenparameter"
  | Symbolic_term.Const constant ->
      Ok (Syntax.Const constant)
  | Symbolic_term.Flex flexible ->
      begin
        match
          List.find_opt
            (fun (candidate, _) ->
              Symbolic_term.equal_flexible
                candidate
                flexible)
            renaming
        with
        | None ->
            Error "answer contains an unregistered residual flexible variable"
        | Some (_, variable) ->
            Ok (Syntax.Var variable)
      end
  | Symbolic_term.Fun (name, arguments) ->
      let rec convert converted = function
        | [] ->
            Ok
              (Syntax.Fun
                 (name, List.rev converted))
        | argument :: rest ->
            begin
              match concretize renaming argument with
              | Error message ->
                  Error message
              | Ok argument ->
                  convert
                    (argument :: converted)
                    rest
            end
      in
      convert [] arguments

let project
    ~avoid
    ~answer_representatives
    ~substitution =
  let images =
    List.map
      (fun (variable, representative) ->
        ( variable,
          Symbolic_substitution.apply
            substitution
            (Symbolic_term.Flex representative) ))
      answer_representatives
  in
  match build_residual_renaming ~avoid images with
  | Error message ->
      Error message
  | Ok renaming ->
      let rec convert answers = function
        | [] ->
            Ok (List.rev answers)
        | (variable, term) :: rest ->
            begin
              match concretize renaming term with
              | Error message ->
                  Error message
              | Ok term ->
                  convert
                    ((variable, term) :: answers)
                    rest
            end
      in
      convert [] images

let project_with_renaming
    ~answer_representatives
    ~substitution
    ~renaming =
  let images =
    List.map
      (fun (variable, representative) ->
        ( variable,
          Symbolic_substitution.apply
            substitution
            (Symbolic_term.Flex representative) ))
      answer_representatives
  in
  let answer_residuals =
    List.concat_map
      (fun (_, term) -> residuals term)
      images
    |> List.sort_uniq Symbolic_term.compare_flexible
  in
  let rec validate_residuals = function
    | [] ->
        Ok ()
    | flexible :: rest ->
        if
          not
            (Substitution.String_set.is_empty
               (Symbolic_term.permission flexible))
        then
          Error
            "answer contains a residual flexible variable with nonempty permission"
        else
          begin
            match
              List.find_opt
                (fun (candidate, _) ->
                  Symbolic_term.equal_flexible
                    candidate
                    flexible)
                renaming
            with
            | None ->
                Error
                  "answer contains a residual flexible variable absent from the global proof renaming"
            | Some _ ->
                validate_residuals rest
          end
  in
  match validate_residuals answer_residuals with
  | Error message ->
      Error message
  | Ok () ->
      let rec convert answers = function
        | [] ->
            Ok (List.rev answers)
        | (variable, term) :: rest ->
            begin
              match concretize renaming term with
              | Error message ->
                  Error message
              | Ok term ->
                  convert
                    ((variable, term) :: answers)
                    rest
            end
      in
      convert [] images
