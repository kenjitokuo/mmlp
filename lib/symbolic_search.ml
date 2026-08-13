type configuration = {
  state : Symbolic_state.t;
  active_eigenparameters : Substitution.String_set.t;
  allocated_proof_parameters : Substitution.String_set.t;
  nested_supply : Nested_sequent.supply;
  symbolic_supply : Symbolic_term.supply;
  node_id : int;
}

let of_root root =
  {
    state = Symbolic_root.state root;
    active_eigenparameters = Substitution.String_set.empty;
    allocated_proof_parameters =
      Symbolic_kernel.proof_parameters (Symbolic_root.state root);
    nested_supply = Symbolic_root.nested_supply root;
    symbolic_supply = Symbolic_root.symbolic_supply root;
    node_id = 0;
  }

let state configuration =
  configuration.state

let active_eigenparameters configuration =
  configuration.active_eigenparameters

let nested_supply configuration =
  configuration.nested_supply

let symbolic_supply configuration =
  configuration.symbolic_supply

let node_id configuration =
  configuration.node_id

let unary_child_id parent =
  (2 * parent) + 1

let left_child_id parent =
  (2 * parent) + 1

let right_child_id parent =
  (2 * parent) + 2

let serial_modalities axioms =
  Modal_axiom.Set.fold
    (fun axiom modalities ->
      match axiom with
      | Modal_axiom.D modality ->
          modality :: modalities
      | _ ->
          modalities)
    axioms
    []
  |> List.sort_uniq Syntax.compare_modal_index
type action =
  | Or_action of Nested_sequent.occurrence_id
  | And_action of Nested_sequent.occurrence_id
  | Exists_action of Nested_sequent.occurrence_id
  | Forall_action of Nested_sequent.occurrence_id * string
  | Box_action of Nested_sequent.occurrence_id
  | Diamond_action of
      Nested_sequent.occurrence_id
      * Nested_sequent.position
      * Modal_certificate.t
  | Seriality_action of
      Nested_sequent.position
      * Syntax.modal_index

let fresh_eigenparameter configuration =
  let used =
    Substitution.String_set.union configuration.allocated_proof_parameters (Symbolic_kernel.proof_parameters configuration.state)
  in
  let rec choose index =
    let candidate =
      "a" ^ string_of_int index
    in
    if Substitution.String_set.mem candidate used then
      choose (index + 1)
    else
      candidate
  in
  choose 0
let available_actions ~environment configuration =
  let state =
    configuration.state
  in
  let grammar =
    Environment.grammar environment
  in
  let occurrences =
    List.sort
      (fun left right ->
        Nested_sequent.compare_occurrence_id
          left.Symbolic_state.occurrence_id
          right.Symbolic_state.occurrence_id)
      (Symbolic_state.formulas state)
  in
  let positions =
    List.sort
      Nested_sequent.compare_position
      (Symbolic_state.positions state)
  in
  let parameter =
    fresh_eigenparameter configuration
  in
  let formula_actions =
    List.concat_map
      (fun occurrence ->
        let occurrence_id =
          occurrence.Symbolic_state.occurrence_id
        in
        match occurrence.Symbolic_state.formula with
        | Symbolic_formula.Or _ ->
            [Or_action occurrence_id]

        | Symbolic_formula.And _ ->
            [And_action occurrence_id]

        | Symbolic_formula.Exists _ ->
            [Exists_action occurrence_id]

        | Symbolic_formula.Forall _ ->
            [Forall_action
               (occurrence_id, parameter)]

        | Symbolic_formula.Box _ ->
            [Box_action occurrence_id]

        | Symbolic_formula.Diamond (modality, _) ->
            List.filter_map
              (fun target ->
                match
                  Certificate_search.find
                    ~grammar
                    ~sequent:(Symbolic_state.tree state)
                    ~modality
                    ~source:occurrence.Symbolic_state.position
                    ~target
                with
                | None ->
                    None
                | Some certificate ->
                    Some
                      (Diamond_action
                         ( occurrence_id,
                           target,
                           certificate )))
              positions

        | Symbolic_formula.PosAtom _
        | Symbolic_formula.NegAtom _
        | Symbolic_formula.Bottom
        | Symbolic_formula.Top ->
            [])
      occurrences
  in
  let seriality_actions =
    List.concat_map
      (fun modality ->
        List.map
          (fun position ->
            Seriality_action
              (position, modality))
          positions)
      (serial_modalities
         (Environment.axioms environment))
  in
  formula_actions @ seriality_actions
type transition =
  | Unary of
      Symbolic_derivation.rule
      * configuration
  | Binary of
      Symbolic_derivation.rule
      * configuration
      * configuration

let apply_action ~environment configuration action =
  let state =
    configuration.state
  in
  match action with
  | Or_action occurrence_id ->
      begin
        match
          Symbolic_kernel.apply_or
            configuration.nested_supply
            state
            occurrence_id
        with
        | None ->
            None
        | Some
            (state, _, _, nested_supply) ->
            Some
              (Unary
                 ( Symbolic_derivation.Or occurrence_id,
                   {
                     configuration with
                     state;
                     nested_supply;
                     node_id =
                       unary_child_id configuration.node_id;
                   } ))
      end

  | And_action occurrence_id ->
      begin
        match
          Symbolic_kernel.apply_and
            configuration.nested_supply
            state
            occurrence_id
        with
        | None ->
            None
        | Some
            ( left_state,
              _,
              right_state,
              _,
              nested_supply ) ->
            Some
              (Binary
                 ( Symbolic_derivation.And occurrence_id,
                   {
                     configuration with
                     state = left_state;
                     nested_supply;
                     node_id =
                       left_child_id configuration.node_id;
                   },
                   {
                     configuration with
                     state = right_state;
                     nested_supply;
                     node_id =
                       right_child_id configuration.node_id;
                   } ))
      end

  | Exists_action occurrence_id ->
      begin
        match
          Symbolic_kernel.apply_exists
            configuration.nested_supply
            configuration.symbolic_supply
            state
            occurrence_id
            ~active_eigenparameters:
              configuration.active_eigenparameters
            ~birth_node:configuration.node_id
        with
        | None ->
            None
        | Some
            ( state,
              _,
              meta,
              nested_supply,
              symbolic_supply ) ->
            Some
              (Unary
                 ( Symbolic_derivation.Exists
                     (occurrence_id, meta),
                   {
                     configuration with
                     state;
                     nested_supply;
                     symbolic_supply;
                     node_id =
                       unary_child_id configuration.node_id;
                   } ))
      end

  | Forall_action (occurrence_id, parameter) ->
      begin
        match
          Symbolic_kernel.apply_forall
            configuration.nested_supply
            state
            occurrence_id
            parameter
        with
        | None ->
            None
        | Some (state, _, nested_supply) ->
            Some
              (Unary
                 ( Symbolic_derivation.Forall
                     (occurrence_id, parameter),
                   {
                     configuration with
                     state;
                     active_eigenparameters =
                       Substitution.String_set.add
                         parameter
                         configuration.active_eigenparameters;
                     allocated_proof_parameters =
                       Substitution.String_set.add
                         parameter
                         configuration.allocated_proof_parameters;
                     nested_supply;
                     node_id =
                       unary_child_id configuration.node_id;
                   } ))
      end

  | Box_action occurrence_id ->
      begin
        match
          Symbolic_kernel.apply_box
            configuration.nested_supply
            state
            occurrence_id
        with
        | None ->
            None
        | Some
            ( state,
              child_position,
              _,
              nested_supply ) ->
            Some
              (Unary
                 ( Symbolic_derivation.Box
                     (occurrence_id, child_position),
                   {
                     configuration with
                     state;
                     nested_supply;
                     node_id =
                       unary_child_id configuration.node_id;
                   } ))
      end

  | Diamond_action
      (occurrence_id, target, certificate) ->
      begin
        match
          Symbolic_kernel.apply_diamond
            configuration.nested_supply
            (Environment.grammar environment)
            state
            occurrence_id
            target
            certificate
        with
        | None ->
            None
        | Some (state, _, nested_supply) ->
            Some
              (Unary
                 ( Symbolic_derivation.Diamond
                     ( occurrence_id,
                       target,
                       certificate ),
                   {
                     configuration with
                     state;
                     nested_supply;
                     node_id =
                       unary_child_id configuration.node_id;
                   } ))
      end

  | Seriality_action (parent, modality) ->
      begin
        match
          Symbolic_kernel.apply_seriality
            configuration.nested_supply
            (Environment.axioms environment)
            state
            parent
            modality
        with
        | None ->
            None
        | Some (state, child_position, nested_supply) ->
            Some
              (Unary
                 ( Symbolic_derivation.Seriality
                     (parent, modality, child_position),
                   {
                     configuration with
                     state;
                     nested_supply;
                     node_id =
                       unary_child_id configuration.node_id;
                   } ))
      end

let terminal_rules configuration =
  if Symbolic_kernel.is_truth_axiom configuration.state then
    [Symbolic_derivation.Truth_leaf]
  else
    List.map
      (fun equations ->
        Symbolic_derivation.Atomic_leaf equations)
      (Symbolic_kernel.atomic_closures
         configuration.state)
type allocation_state = {
  allocated_proof_parameters :
    Substitution.String_set.t;
  allocated_nested_supply :
    Nested_sequent.supply;
  allocated_symbolic_supply :
    Symbolic_term.supply;
}

let allocation_state_of_configuration (configuration : configuration) =
  {
    allocated_proof_parameters =
      configuration.allocated_proof_parameters;
    allocated_nested_supply =
      configuration.nested_supply;
    allocated_symbolic_supply =
      configuration.symbolic_supply;
  }

let with_allocation_state (allocation : allocation_state) (configuration : configuration) =
  {
    configuration with
    allocated_proof_parameters =
      allocation.allocated_proof_parameters;
    nested_supply =
      allocation.allocated_nested_supply;
    symbolic_supply =
      allocation.allocated_symbolic_supply;
  }

let derivations_within_depth
    ~environment
    ~depth
    configuration =
  let rec derive depth configuration =
    let terminal_derivations =
      let allocation =
        allocation_state_of_configuration configuration
      in
      List.map
        (fun rule ->
          ( Symbolic_derivation.make
              ~node_id:configuration.node_id
              ~conclusion:configuration.state
              ~rule
              ~premises:[],
            allocation ))
        (terminal_rules configuration)
    in
    if depth = 0 then
      terminal_derivations
    else
      let nonterminal_derivations =
        List.concat_map
          (fun action ->
            match
              apply_action
                ~environment
                configuration
                action
            with
            | None ->
                []

            | Some (Unary (rule, child)) ->
                derive
                  (depth - 1)
                  child
                |> List.map
                     (fun (premise, allocation) ->
                       ( Symbolic_derivation.make
                           ~node_id:configuration.node_id
                           ~conclusion:configuration.state
                           ~rule
                           ~premises:[premise],
                         allocation ))

            | Some (Binary (rule, left, right)) ->
                derive
                  (depth - 1)
                  left
                |> List.concat_map
                     (fun (left_premise, allocation_after_left) ->
                       let right =
                         with_allocation_state
                           allocation_after_left
                           right
                       in
                       derive
                         (depth - 1)
                         right
                       |> List.map
                            (fun
                              ( right_premise,
                                allocation_after_right ) ->
                              ( Symbolic_derivation.make
                                  ~node_id:configuration.node_id
                                  ~conclusion:configuration.state
                                  ~rule
                                  ~premises:
                                    [ left_premise;
                                      right_premise ],
                                allocation_after_right ))))
          (available_actions
             ~environment
             configuration)
      in
      terminal_derivations @ nonterminal_derivations
  in
  derive depth configuration
  |> List.map fst
type solved_derivation = {
  derivation : Symbolic_derivation.t;
  substitution : Symbolic_substitution.t;
}

let solve_derivation derivation =
  let constraints =
    Symbolic_derivation.atomic_constraints derivation
  in
  let flexibles =
    List.concat_map
      (fun (left, right) ->
        Symbolic_term.flexible_variables left
        @ Symbolic_term.flexible_variables right)
      constraints
    |> List.sort_uniq Symbolic_term.compare_flexible
  in
  let supply =
    Symbolic_term.supply_after flexibles
  in
  match
    Scoped_unification.solve
      ~supply
      constraints
  with
  | Scoped_unification.Unsolvable ->
      None
  | Scoped_unification.Solved (substitution, _) ->
      Some
        {
          derivation;
          substitution;
        }
let names_to_avoid derivation =
  let rec collect derivation =
    let state =
      Symbolic_derivation.conclusion derivation
    in
    let local =
      List.fold_left
        (fun names occurrence ->
          Substitution.String_set.union
            names
            (Substitution.String_set.union
               (Symbolic_formula.ordinary_variables
                  occurrence.Symbolic_state.formula)
               (Symbolic_formula.proof_parameters
                  occurrence.Symbolic_state.formula)))
        Substitution.String_set.empty
        (Symbolic_state.formulas state)
    in
    List.fold_left
      (fun names premise ->
        Substitution.String_set.union
          names
          (collect premise))
      local
      (Symbolic_derivation.premises derivation)
  in
  collect derivation
let project_solved_derivation ~root solved =
  let avoid =
    List.fold_left
      (fun names (variable, _) ->
        Substitution.String_set.add variable names)
      (names_to_avoid solved.derivation)
      (Symbolic_root.answer_representatives root)
  in
  Answer_projection.project
    ~avoid
    ~answer_representatives:
      (Symbolic_root.answer_representatives root)
    ~substitution:solved.substitution
type computed_answer = {
  answer : Answer_projection.answer;
  derivation : Symbolic_derivation.t;
  substitution : Symbolic_substitution.t;
}

let answers_within_depth
    ~environment
    ~root
    ~depth =
  let configuration =
    of_root root
  in
  List.filter_map
    (fun derivation ->
      match solve_derivation derivation with
      | None ->
          None
      | Some solved ->
          begin
            match
              project_solved_derivation
                ~root
                solved
            with
            | Error _ ->
                None
            | Ok answer ->
                Some
                  {
                    answer;
                    derivation = solved.derivation;
                    substitution = solved.substitution;
                  }
          end)
    (derivations_within_depth
       ~environment
       ~depth
       configuration)
let answers_at_exact_depth
    ~environment
    ~root
    ~depth =
  answers_within_depth
    ~environment
    ~root
    ~depth
  |> List.filter
       (fun computed ->
         Symbolic_derivation.height
           computed.derivation
         = depth)
let iterative_deepening
    ~environment
    ~root =
  let rec from_depth depth () =
    let current =
      answers_at_exact_depth
        ~environment
        ~root
        ~depth
    in
    Seq.append
      (List.to_seq current)
      (from_depth (depth + 1))
      ()
  in
  from_depth 0





let allocated_proof_parameters (configuration : configuration) =
  configuration.allocated_proof_parameters

let with_allocated_proof_parameters
    allocated_proof_parameters
    (configuration : configuration) =
  {
    configuration with
    allocated_proof_parameters;
  }
