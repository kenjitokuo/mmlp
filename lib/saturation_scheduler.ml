module Int_set = Set.Make (Int)

type obligation =
  | Or of Nested_sequent.occurrence_id
  | And of Nested_sequent.occurrence_id
  | Forall of Nested_sequent.occurrence_id
  | Exists of Nested_sequent.occurrence_id * int
  | Box of Nested_sequent.occurrence_id
  | Diamond of
      Nested_sequent.occurrence_id
      * Syntax.modal_index
      * Nested_sequent.position
      * Nested_sequent.position
  | Seriality of Syntax.modal_index * Nested_sequent.position

type configuration = {
  state : Nested_sequent.t;
  history : Int_set.t;
  stage : int;
  supply : Nested_sequent.supply;
}

type transition =
  | Closed of Derivation.t
  | Bookkeeping of configuration
  | Applied of {
      obligation : obligation;
      code : int;
      rule : Derivation.rule;
      successors : configuration list;
    }

let state configuration =
  configuration.state

let history configuration =
  Int_set.elements configuration.history

let stage configuration =
  configuration.stage

let rec advance_positions supply remaining =
  if remaining <= 0 then
    supply
  else
    let _, supply =
      Nested_sequent.fresh_position supply
    in
    advance_positions supply (remaining - 1)

let rec advance_occurrences supply remaining =
  if remaining <= 0 then
    supply
  else
    let _, supply =
      Nested_sequent.fresh_occurrence_id supply
    in
    advance_occurrences supply (remaining - 1)

let supply_after_state sequent =
  let next_position =
    List.fold_left
      (fun maximum position ->
        max
          maximum
          (Nested_sequent.position_number position + 1))
      0
      (Nested_sequent.position_ids sequent)
  in
  let next_occurrence =
    List.fold_left
      (fun maximum occurrence_id ->
        max
          maximum
          (Nested_sequent.occurrence_id_number occurrence_id + 1))
      0
      (Nested_sequent.occurrence_ids sequent)
  in
  Nested_sequent.initial_supply
  |> fun supply -> advance_positions supply next_position
  |> fun supply -> advance_occurrences supply next_occurrence

let create sequent =
  {
    state = sequent;
    history = Int_set.empty;
    stage = 0;
    supply = supply_after_state sequent;
  }

let pair left right =
  let sum = left + right in
  ((sum * (sum + 1)) / 2) + right

let tagged tag payload =
  (7 * payload) + tag

let obligation_code = function
  | Or occurrence_id ->
      tagged
        0
        (Nested_sequent.occurrence_id_number occurrence_id)

  | And occurrence_id ->
      tagged
        1
        (Nested_sequent.occurrence_id_number occurrence_id)

  | Forall occurrence_id ->
      tagged
        2
        (Nested_sequent.occurrence_id_number occurrence_id)

  | Exists (occurrence_id, term_index) ->
      tagged
        3
        (pair
           (Nested_sequent.occurrence_id_number occurrence_id)
           term_index)

  | Box occurrence_id ->
      tagged
        4
        (Nested_sequent.occurrence_id_number occurrence_id)

  | Diamond
      (occurrence_id, modality, source, target) ->
      tagged
        5
        (pair
           (Nested_sequent.occurrence_id_number occurrence_id)
           (pair
              (Syntax.modal_index_number modality)
              (pair
                 (Nested_sequent.position_number source)
                 (Nested_sequent.position_number target))))

  | Seriality (modality, source) ->
      tagged
        6
        (pair
           (Syntax.modal_index_number modality)
           (Nested_sequent.position_number source))

let compare_obligation left right =
  Int.compare
    (obligation_code left)
    (obligation_code right)

let identifier_alphabet =
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_0123456789"

let identifier_of_index index =
  if index < 0 then
    invalid_arg "negative identifier index"
  else
    let base =
      String.length identifier_alphabet
    in
    let rec collect value characters =
      let digit =
        value mod base
      in
      let characters =
        identifier_alphabet.[digit] :: characters
      in
      let quotient =
        value / base
      in
      if quotient = 0 then
        characters
      else
        collect (quotient - 1) characters
    in
    collect index []
    |> List.to_seq
    |> String.of_seq

let unpair index =
  if index < 0 then
    invalid_arg "negative pairing index"
  else if index = max_int then
    invalid_arg "pairing index is too large"
  else
    let rec split twos odd =
      if odd mod 2 = 0 then
        split (twos + 1) (odd / 2)
      else
        twos, (odd - 1) / 2
    in
    split 0 (index + 1)

let rec proof_term signature index =
  if index < 0 then
    invalid_arg "negative proof-term index"
  else
    let tag, payload =
      unpair index
    in
    if tag = 0 then
      Syntax.Var (identifier_of_index payload)
    else if tag = 1 then
      Syntax.Param (identifier_of_index payload)
    else
      let constants =
        Signature.constants signature
      in
      let functions =
        Signature.functions signature
      in
      let constructor_index =
        tag - 2
      in
      let constant_count =
        List.length constants
      in
      if constructor_index < constant_count then
        Syntax.Const
          (List.nth constants constructor_index)
      else
        let function_index =
          constructor_index - constant_count
        in
        match List.nth_opt functions function_index with
        | None ->
            Syntax.Var
              (identifier_of_index index)
        | Some (name, arity) ->
            Syntax.Fun
              ( name,
                proof_term_arguments
                  signature
                  arity
                  payload )

and proof_term_arguments signature arity payload =
  if arity <= 0 then
    []
  else
    let argument_index, remainder =
      unpair payload
    in
    proof_term signature argument_index
    ::
    proof_term_arguments
      signature
      (arity - 1)
      remainder

let rec occurrences_with_positions sequent =
  let here =
    List.map
      (fun occurrence ->
        sequent.Nested_sequent.position,
        occurrence)
      sequent.Nested_sequent.formulas
  in
  let below =
    List.concat_map
      (fun child ->
        occurrences_with_positions
          child.Nested_sequent.subtree)
      sequent.Nested_sequent.children
  in
  here @ below

let sorted_positions sequent =
  Nested_sequent.position_ids sequent
  |> List.sort Nested_sequent.compare_position

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
  |> List.sort Syntax.compare_modal_index

let eligible configuration obligation =
  let code =
    obligation_code obligation
  in
  code <= configuration.stage
  && not
       (Int_set.mem
          code
          configuration.history)

let add_if_eligible configuration obligation obligations =
  if eligible configuration obligation then
    obligation :: obligations
  else
    obligations

let exists_obligations configuration occurrence_id =
  let rec collect term_index obligations =
    let obligation =
      Exists (occurrence_id, term_index)
    in
    let code =
      obligation_code obligation
    in
    if code > configuration.stage then
      List.rev obligations
    else
      let obligations =
        if
          Int_set.mem
            code
            configuration.history
        then
          obligations
        else
          obligation :: obligations
      in
      collect (term_index + 1) obligations
  in
  collect 0 []

let available_obligations ~environment configuration =
  let sequent =
    configuration.state
  in
  let grammar =
    Environment.grammar environment
  in
  let positions =
    sorted_positions sequent
  in
  let formula_obligations =
    occurrences_with_positions sequent
    |> List.fold_left
         (fun obligations (source, occurrence) ->
           let occurrence_id =
             occurrence.Nested_sequent.occurrence_id
           in
           match occurrence.Nested_sequent.formula with
           | Syntax.CoreOr _ ->
               add_if_eligible
                 configuration
                 (Or occurrence_id)
                 obligations

           | Syntax.CoreAnd _ ->
               add_if_eligible
                 configuration
                 (And occurrence_id)
                 obligations

           | Syntax.CoreForall _ ->
               add_if_eligible
                 configuration
                 (Forall occurrence_id)
                 obligations

           | Syntax.CoreExists _ ->
               List.rev_append
                 (exists_obligations
                    configuration
                    occurrence_id)
                 obligations

           | Syntax.CoreBox _ ->
               add_if_eligible
                 configuration
                 (Box occurrence_id)
                 obligations

           | Syntax.CoreDiamond (modality, _) ->
               List.fold_left
                 (fun obligations target ->
                   match
                     Certificate_search.find
                       ~grammar
                       ~sequent
                       ~modality
                       ~source
                       ~target
                   with
                   | None ->
                       obligations
                   | Some _ ->
                       add_if_eligible
                         configuration
                         (Diamond
                            ( occurrence_id,
                              modality,
                              source,
                              target ))
                         obligations)
                 obligations
                 positions

           | Syntax.PosAtom _
           | Syntax.NegAtom _
           | Syntax.CoreBottom
           | Syntax.CoreTop ->
               obligations)
         []
  in
  let seriality_obligations =
    serial_modalities
      (Environment.axioms environment)
    |> List.fold_left
         (fun obligations modality ->
           List.fold_left
             (fun obligations source ->
               add_if_eligible
                 configuration
                 (Seriality (modality, source))
                 obligations)
             obligations
             positions)
         []
  in
  formula_obligations
  @ seriality_obligations
  |> List.sort compare_obligation

let fresh_proof_parameter sequent =
  let used =
    Nested_sequent.proof_params sequent
  in
  let rec choose index =
    let parameter =
      "a" ^ string_of_int index
    in
    if
      Substitution.String_set.mem
        parameter
        used
    then
      choose (index + 1)
    else
      parameter
  in
  choose 0

let successor
    configuration
    ~history
    ~supply
    state =
  {
    state;
    history;
    stage = configuration.stage + 1;
    supply;
  }

let bookkeeping configuration =
  {
    configuration with
    stage = configuration.stage + 1;
  }

let applied
    configuration
    obligation
    rule
    history
    supply
    states =
  Applied
    {
      obligation;
      code = obligation_code obligation;
      rule;
      successors =
        List.map
          (successor
             configuration
             ~history
             ~supply)
          states;
    }

let apply_and_canonical supply sequent occurrence_id =
  match Nested_sequent.find_occurrence sequent occurrence_id with
  | Some (position, occurrence) ->
      begin
        match occurrence.Nested_sequent.formula with
        | Syntax.CoreAnd (left, right) ->
            begin
              match
                Nested_sequent.remove_occurrence
                  sequent
                  occurrence_id
              with
              | None ->
                  None
              | Some base ->
                  begin
                    match
                      Nested_sequent.add_formula
                        supply
                        base
                        position
                        left
                    with
                    | None ->
                        None
                    | Some
                        (left_state,
                         left_occurrence,
                         left_supply) ->
                        begin
                          match
                            Nested_sequent.add_formula
                              supply
                              base
                              position
                              right
                          with
                          | None ->
                              None
                          | Some
                              (right_state,
                               right_occurrence,
                               right_supply) ->
                              Some
                                ( left_state,
                                  left_occurrence,
                                  left_supply,
                                  right_state,
                                  right_occurrence,
                                  right_supply )
                        end
                  end
            end
        | _ ->
            None
      end
  | None ->
      None
let step ~environment configuration =
  let sequent =
    configuration.state
  in
  if Kernel.is_truth_axiom sequent then
    Ok
      (Closed
         {
           Derivation.conclusion = sequent;
           rule = Derivation.Truth_axiom;
           premises = [];
         })
  else if Kernel.is_atomic_axiom sequent then
    Ok
      (Closed
         {
           Derivation.conclusion = sequent;
           rule = Derivation.Atomic_axiom;
           premises = [];
         })
  else
    match
      available_obligations
        ~environment
        configuration
    with
    | [] ->
        Ok
          (Bookkeeping
             (bookkeeping configuration))

    | obligation :: _ ->
        let code =
          obligation_code obligation
        in
        let history =
          Int_set.add
            code
            configuration.history
        in
        begin
          match obligation with
          | Or occurrence_id ->
              begin
                match
                  Kernel.apply_or
                    configuration.supply
                    sequent
                    occurrence_id
                with
                | None ->
                    Error
                      "saturation scheduler: failed to apply disjunction obligation"
                | Some
                    ( premise,
                      _,
                      _,
                      supply ) ->
                    Ok
                      (applied
                         configuration
                         obligation
                         (Derivation.Or occurrence_id)
                         history
                         supply
                         [premise])
              end

          | And occurrence_id ->
              begin
                match
                  apply_and_canonical
                    configuration.supply
                    sequent
                    occurrence_id
                with
                | None ->
                    Error
                      "saturation scheduler: failed to apply conjunction obligation"
                | Some
                    ( premise_left,
                      _,
                      left_supply,
                      premise_right,
                      _,
                      right_supply ) ->
                    let left =
                      successor
                        configuration
                        ~history
                        ~supply:left_supply
                        premise_left
                    in
                    let right =
                      successor
                        configuration
                        ~history
                        ~supply:right_supply
                        premise_right
                    in
                    Ok
                      (Applied
                         {
                           obligation;
                           code;
                           rule = Derivation.And occurrence_id;
                           successors = [left; right];
                         })
              end

          | Exists
              (occurrence_id, term_index) ->
              let witness =
                proof_term
                  (Environment.signature environment)
                  term_index
              in
              begin
                match
                  Kernel.apply_exists
                    configuration.supply
                    sequent
                    occurrence_id
                    witness
                with
                | None ->
                    Error
                      "saturation scheduler: failed to apply existential obligation"
                | Some
                    ( premise,
                      _,
                      supply ) ->
                    Ok
                      (applied
                         configuration
                         obligation
                         (Derivation.Exists
                            (occurrence_id, witness))
                         history
                         supply
                         [premise])
              end

          | Forall occurrence_id ->
              let parameter =
                fresh_proof_parameter sequent
              in
              begin
                match
                  Kernel.apply_forall
                    configuration.supply
                    sequent
                    occurrence_id
                    parameter
                with
                | None ->
                    Error
                      "saturation scheduler: failed to apply universal obligation"
                | Some
                    ( premise,
                      _,
                      supply ) ->
                    Ok
                      (applied
                         configuration
                         obligation
                         (Derivation.Forall
                            (occurrence_id, parameter))
                         history
                         supply
                         [premise])
              end

          | Box occurrence_id ->
              begin
                match
                  Kernel.apply_box
                    configuration.supply
                    sequent
                    occurrence_id
                with
                | None ->
                    Error
                      "saturation scheduler: failed to apply box obligation"
                | Some
                    ( premise,
                      child_position,
                      _,
                      supply ) ->
                    Ok
                      (applied
                         configuration
                         obligation
                         (Derivation.Box
                            ( occurrence_id,
                              child_position ))
                         history
                         supply
                         [premise])
              end

          | Diamond
              ( occurrence_id,
                modality,
                source,
                target ) ->
              let grammar =
                Environment.grammar environment
              in
              begin
                match
                  Certificate_search.find
                    ~grammar
                    ~sequent
                    ~modality
                    ~source
                    ~target
                with
                | None ->
                    Error
                      "saturation scheduler: diamond obligation lost its certificate"
                | Some certificate ->
                    begin
                      match
                        Kernel.apply_diamond
                          configuration.supply
                          grammar
                          sequent
                          occurrence_id
                          target
                          certificate
                      with
                      | None ->
                          Error
                            "saturation scheduler: failed to apply diamond obligation"
                      | Some
                          ( premise,
                            _,
                            supply ) ->
                          Ok
                            (applied
                               configuration
                               obligation
                               (Derivation.Diamond
                                  ( occurrence_id,
                                    target,
                                    certificate ))
                               history
                               supply
                               [premise])
                    end
              end

          | Seriality (modality, source) ->
              begin
                match
                  Kernel.apply_seriality
                    configuration.supply
                    (Environment.axioms environment)
                    sequent
                    source
                    modality
                with
                | None ->
                    Error
                      "saturation scheduler: failed to apply seriality obligation"
                | Some
                    ( premise,
                      child_position,
                      supply ) ->
                    Ok
                      (applied
                         configuration
                         obligation
                         (Derivation.Seriality
                            ( source,
                              modality,
                              child_position ))
                         history
                         supply
                         [premise])
              end
        end

let proof_within_steps
    ~environment
    ~max_steps
    initial =
  if max_steps < 0 then
    None
  else
    let rec search remaining configuration =
      match step ~environment configuration with
      | Error _ ->
          None

      | Ok (Closed derivation) ->
          Some derivation

      | Ok (Bookkeeping successor) ->
          if remaining = 0 then
            None
          else
            search
              (remaining - 1)
              successor

      | Ok
          (Applied
             {
               rule;
               successors;
               _;
             }) ->
          if remaining = 0 then
            None
          else
            let rec prove_all proofs = function
              | [] ->
                  Some (List.rev proofs)
              | successor :: rest ->
                  begin
                    match
                      search
                        (remaining - 1)
                        successor
                    with
                    | None ->
                        None
                    | Some proof ->
                        prove_all
                          (proof :: proofs)
                          rest
                  end
            in
            begin
              match prove_all [] successors with
              | None ->
                  None
              | Some premises ->
                  Some
                    {
                      Derivation.conclusion =
                        configuration.state;
                      rule;
                      premises;
                    }
            end
    in
    match search max_steps initial with
    | Some derivation
        when Environment.check_derivation
               environment
               derivation ->
        Some derivation
    | _ ->
        None
