type equation =
  Symbolic_term.term * Symbolic_term.term

type result =
  | Solved of Symbolic_substitution.t * Symbolic_term.supply
  | Unsolvable

module Flexible_set =
  Set.Make (struct
    type t = Symbolic_term.flexible_variable

    let compare =
      Symbolic_term.compare_flexible
  end)

let rec equal_term left right =
  match left, right with
  | Symbolic_term.Var x, Symbolic_term.Var y
  | Symbolic_term.Param x, Symbolic_term.Param y
  | Symbolic_term.Const x, Symbolic_term.Const y ->
      String.equal x y
  | Symbolic_term.Flex x, Symbolic_term.Flex y ->
      Symbolic_term.equal_flexible x y
  | Symbolic_term.Fun (f, left_arguments),
    Symbolic_term.Fun (g, right_arguments) ->
      String.equal f g
      && List.length left_arguments = List.length right_arguments
      && List.for_all2 equal_term left_arguments right_arguments
  | _ ->
      false

let unique_flexible_variables term =
  List.sort_uniq
    Symbolic_term.compare_flexible
    (Symbolic_term.flexible_variables term)

let first_forbidden_dependency flexible term =
  List.find_opt
    (fun dependency ->
      not
        (Substitution.String_set.subset
           (Symbolic_term.permission dependency)
           (Symbolic_term.permission flexible)))
    (unique_flexible_variables term)

let singleton_substitution flexible term =
  Symbolic_substitution.bind
    Symbolic_substitution.empty
    flexible
    term

let apply_to_equations substitution equations =
  List.map
    (fun (left, right) ->
      ( Symbolic_substitution.apply substitution left,
        Symbolic_substitution.apply substitution right ))
    equations

let flexible_variables_of_equations equations =
  List.fold_left
    (fun current (left, right) ->
      let add_term current term =
        List.fold_left
          (fun current flexible ->
            Flexible_set.add flexible current)
          current
          (Symbolic_term.flexible_variables term)
      in
      add_term (add_term current left) right)
    Flexible_set.empty
    equations

let flexible_set_of_term term =
  List.fold_left
    (fun variables flexible ->
      Flexible_set.add flexible variables)
    Flexible_set.empty
    (Symbolic_term.flexible_variables term)

let current_supports_equations current equations =
  List.for_all
    (fun (left, right) ->
      Flexible_set.subset
        (Flexible_set.union
           (flexible_set_of_term left)
           (flexible_set_of_term right))
        current)
    equations

let solve ~supply equations =
  let rec loop supply current accumulator equations =
    if not (current_supports_equations current equations) then
      failwith "Scoped_unification: current-support invariant violated"
    else
      match equations with
    | [] ->
        Solved (accumulator, supply)

    | (left, right) :: rest when equal_term left right ->
        loop supply current accumulator rest

    | (Symbolic_term.Fun (left_name, left_arguments),
       Symbolic_term.Fun (right_name, right_arguments)) :: rest
      when String.equal left_name right_name
           && List.length left_arguments = List.length right_arguments ->
        loop
          supply
          current
          accumulator
          (List.combine left_arguments right_arguments @ rest)

    | (left, Symbolic_term.Flex flexible) :: rest ->
        begin
          match left with
          | Symbolic_term.Flex _ ->
              solve_flexible
                supply
                current
                accumulator
                flexible
                left
                rest
          | _ ->
              solve_flexible
                supply
                current
                accumulator
                flexible
                left
                rest
        end

    | (Symbolic_term.Flex flexible, term) :: rest ->
        solve_flexible
          supply
          current
          accumulator
          flexible
          term
          rest

    | _ ->
        Unsolvable

  and solve_flexible supply current accumulator flexible term rest =
    if
      Symbolic_substitution.occurs flexible term
      && not (equal_term (Symbolic_term.Flex flexible) term)
    then
      Unsolvable
    else if
      not
        (Substitution.String_set.subset
           (Symbolic_term.proof_parameters term)
           (Symbolic_term.permission flexible))
    then
      Unsolvable
    else
      match first_forbidden_dependency flexible term with
      | Some dependency ->
          let restricted_permission =
            Substitution.String_set.inter
              (Symbolic_term.permission dependency)
              (Symbolic_term.permission flexible)
          in
          let replacement, supply =
            Symbolic_term.fresh_restriction
              supply
              ~permission:restricted_permission
          in
          begin
            match
              singleton_substitution
                dependency
                (Symbolic_term.Flex replacement)
            with
            | None ->
                Unsolvable
            | Some delta ->
                begin
                  match
                    Symbolic_substitution.bind
                      accumulator
                      dependency
                      (Symbolic_term.Flex replacement)
                  with
                  | None ->
                      Unsolvable
                  | Some accumulator ->
                      let current =
                        current
                        |> Flexible_set.remove dependency
                        |> Flexible_set.add replacement
                      in
                      let equations =
                        apply_to_equations
                          delta
                          ((Symbolic_term.Flex flexible, term) :: rest)
                      in
                      loop
                        supply
                        current
                        accumulator
                        equations
                end
          end

      | None ->
          if not (Symbolic_term.safe_for flexible term) then
            Unsolvable
          else
            begin
              match singleton_substitution flexible term with
              | None ->
                  Unsolvable
              | Some delta ->
                  begin
                    match
                      Symbolic_substitution.bind
                        accumulator
                        flexible
                        term
                    with
                    | None ->
                        Unsolvable
                    | Some accumulator ->
                        let current =
                          Flexible_set.remove flexible current
                        in
                        loop
                          supply
                          current
                          accumulator
                          (apply_to_equations delta rest)
                  end
            end
  in
  let current =
    flexible_variables_of_equations equations
  in
  loop
    supply
    current
    Symbolic_substitution.empty
    equations
