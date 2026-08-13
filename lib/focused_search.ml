let is_asynchronous_action = function
  | Symbolic_search.Or_action _
  | Symbolic_search.And_action _
  | Symbolic_search.Forall_action _
  | Symbolic_search.Box_action _ ->
      true
  | Symbolic_search.Exists_action _
  | Symbolic_search.Diamond_action _
  | Symbolic_search.Seriality_action _ ->
      false

let is_focus_start = function
  | Symbolic_search.Exists_action _
  | Symbolic_search.Diamond_action _
  | Symbolic_search.Seriality_action _ ->
      true
  | _ ->
      false

let same_occurrence left right =
  Nested_sequent.compare_occurrence_id left right = 0

let new_occurrences before after =
  let old_ids =
    List.map
      (fun occurrence ->
        occurrence.Symbolic_state.occurrence_id)
      (Symbolic_state.formulas before)
  in
  List.filter
    (fun occurrence ->
      not
        (List.exists
           (same_occurrence
              occurrence.Symbolic_state.occurrence_id)
           old_ids))
    (Symbolic_state.formulas after)

let newly_introduced_occurrence before after =
  match new_occurrences before after with
  | [occurrence] ->
      Some occurrence
  | _ ->
      None

let terminal_derivations configuration =
  List.map
    (fun rule ->
      Symbolic_derivation.make
        ~node_id:(Symbolic_search.node_id configuration)
        ~conclusion:(Symbolic_search.state configuration)
        ~rule
        ~premises:[])
    (Symbolic_search.terminal_rules configuration)

let make_unary configuration rule premise =
  Symbolic_derivation.make
    ~node_id:(Symbolic_search.node_id configuration)
    ~conclusion:(Symbolic_search.state configuration)
    ~rule
    ~premises:[premise]

let make_binary configuration rule left right =
  Symbolic_derivation.make
    ~node_id:(Symbolic_search.node_id configuration)
    ~conclusion:(Symbolic_search.state configuration)
    ~rule
    ~premises:[left; right]

let cartesian_make_binary configuration rule lefts rights =
  List.concat_map
    (fun left ->
      List.map
        (fun right ->
          make_binary configuration rule left right)
        rights)
    lefts

let continuation_actions
    ~environment
    occurrence
    configuration =
  match occurrence.Symbolic_state.formula with
  | Symbolic_formula.Exists _ ->
      Symbolic_search.available_actions
        ~environment
        configuration
      |> List.filter
           (function
             | Symbolic_search.Exists_action occurrence_id ->
                 same_occurrence
                   occurrence.Symbolic_state.occurrence_id
                   occurrence_id
             | _ ->
                 false)
  | Symbolic_formula.Diamond _ ->
      Symbolic_search.available_actions
        ~environment
        configuration
      |> List.filter
           (function
             | Symbolic_search.Diamond_action
                 (occurrence_id, _, _) ->
                 same_occurrence
                   occurrence.Symbolic_state.occurrence_id
                   occurrence_id
             | _ ->
                 false)
  | _ ->
      []

let derivations_within_depth
    ~environment
    ~depth
    root_configuration =
  let terminal_results configuration =
    let allocated =
      Symbolic_search.allocation_state_of_configuration
        configuration
    in
    terminal_derivations configuration
    |> List.map
         (fun derivation ->
           (derivation, allocated))
  in

  let rec derive_main depth configuration =
    let terminals =
      terminal_results configuration
    in
    if depth = 0 then
      terminals
    else
      let asynchronous_actions =
        Symbolic_search.available_actions
          ~environment
          configuration
        |> List.filter is_asynchronous_action
      in
      match asynchronous_actions with
      | action :: _ ->
          terminals
          @ derive_asynchronous_action
              depth
              configuration
              action
      | [] ->
          let focus_starts =
            Symbolic_search.available_actions
              ~environment
              configuration
            |> List.filter is_focus_start
          in
          terminals
          @ List.concat_map
              (derive_focus_start
                 depth
                 configuration)
              focus_starts

  and derive_asynchronous_action
      depth
      configuration
      action =
    match
      Symbolic_search.apply_action
        ~environment
        configuration
        action
    with
    | None ->
        []

    | Some (Symbolic_search.Unary (rule, child)) ->
        derive_main
          (depth - 1)
          child
        |> List.map
             (fun (premise, allocated) ->
               ( make_unary
                   configuration
                   rule
                   premise,
                 allocated ))

    | Some
        (Symbolic_search.Binary
           (rule, left_child, right_child)) ->
        derive_main
          (depth - 1)
          left_child
        |> List.concat_map
             (fun (left, allocated_after_left) ->
               let right_child =
                 Symbolic_search.with_allocation_state
                   allocated_after_left
                   right_child
               in
               derive_main
                 (depth - 1)
                 right_child
               |> List.map
                    (fun (right, allocated_after_right) ->
                      ( make_binary
                          configuration
                          rule
                          left
                          right,
                        allocated_after_right )))

  and derive_focus_start
      depth
      configuration
      action =
    match
      Symbolic_search.apply_action
        ~environment
        configuration
        action
    with
    | None ->
        []

    | Some (Symbolic_search.Binary _) ->
        []

    | Some (Symbolic_search.Unary (rule, child)) ->
        begin
          match action with
          | Symbolic_search.Seriality_action _ ->
              derive_main
                (depth - 1)
                child
              |> List.map
                   (fun (premise, allocated) ->
                     ( make_unary
                         configuration
                         rule
                         premise,
                       allocated ))

          | Symbolic_search.Exists_action _
          | Symbolic_search.Diamond_action _ ->
              begin
                match
                  newly_introduced_occurrence
                    (Symbolic_search.state configuration)
                    (Symbolic_search.state child)
                with
                | None ->
                    []

                | Some distinguished ->
                    derive_focus_continuation
                      (depth - 1)
                      child
                      distinguished
                    |> List.map
                         (fun (premise, allocated) ->
                           ( make_unary
                               configuration
                               rule
                               premise,
                             allocated ))
              end

          | _ ->
              []
        end

  and derive_focus_continuation
      depth
      configuration
      distinguished =
    let terminals =
      terminal_results configuration
    in
    if depth = 0 then
      terminals
    else
      let actions =
        continuation_actions
          ~environment
          distinguished
          configuration
      in
      match distinguished.Symbolic_state.formula with
      | Symbolic_formula.Exists _ ->
          begin
            match actions with
            | [] ->
                terminals
                @ derive_main
                    depth
                    configuration

            | action :: _ ->
                terminals
                @ derive_focus_step
                    depth
                    configuration
                    action
          end

      | Symbolic_formula.Diamond _ ->
          if actions = [] then
            terminals
            @ derive_main
                depth
                configuration
          else
            terminals
            @ List.concat_map
                (derive_focus_step
                   depth
                   configuration)
                actions

      | _ ->
          terminals
          @ derive_main
              depth
              configuration

  and derive_focus_step
      depth
      configuration
      action =
    match
      Symbolic_search.apply_action
        ~environment
        configuration
        action
    with
    | None ->
        []

    | Some (Symbolic_search.Binary _) ->
        []

    | Some (Symbolic_search.Unary (rule, child)) ->
        begin
          match
            newly_introduced_occurrence
              (Symbolic_search.state configuration)
              (Symbolic_search.state child)
          with
          | None ->
              []

          | Some distinguished ->
              derive_focus_continuation
                (depth - 1)
                child
                distinguished
              |> List.map
                   (fun (premise, allocated) ->
                     ( make_unary
                         configuration
                         rule
                         premise,
                       allocated ))
        end
  in
  derive_main depth root_configuration
  |> List.map fst

let solve_derivation =
  Symbolic_search.solve_derivation

let answers_within_depth
    ~environment
    ~root
    ~depth =
  derivations_within_depth
    ~environment
    ~depth
    (Symbolic_search.of_root root)
  |> List.filter_map
       (fun derivation ->
         match solve_derivation derivation with
         | None ->
             None
         | Some solved ->
             begin
               match
                 Trusted_answer.certify
                   ~environment
                   ~root
                   solved
               with
               | Error _ ->
                   None
               | Ok answer ->
                   Some answer
             end)

let answers_at_exact_depth
    ~environment
    ~root
    ~depth =
  answers_within_depth
    ~environment
    ~root
    ~depth
  |> List.filter
       (fun answer ->
         Symbolic_derivation.height
           answer.Trusted_answer.symbolic_derivation
         = depth)

let iterative_deepening
    ~environment
    ~root =
  let rec enumerate depth () =
    Seq.append
      (List.to_seq
         (answers_at_exact_depth
            ~environment
            ~root
            ~depth))
      (enumerate (depth + 1))
      ()
  in
  enumerate 0
