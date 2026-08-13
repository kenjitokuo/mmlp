type formula_occurrence = {
  occurrence_id : Nested_sequent.occurrence_id;
  position : Nested_sequent.position;
  formula : Symbolic_formula.t;
}

type t = {
  tree : Nested_sequent.t;
  formulas : formula_occurrence list;
}

let tree state =
  state.tree

let formulas state =
  state.formulas

let create_root supply initial_formulas =
  let root_position, supply =
    Nested_sequent.fresh_position supply
  in
  let tree : Nested_sequent.t =
    {
      position = root_position;
      formulas = [];
      children = [];
    }
  in
  let rec add_initial supply occurrences = function
    | [] ->
        ( { tree; formulas = List.rev occurrences },
          root_position,
          supply )
    | formula :: rest ->
        let occurrence_id, supply =
          Nested_sequent.fresh_occurrence_id supply
        in
        let occurrence =
          {
            occurrence_id;
            position = root_position;
            formula;
          }
        in
        add_initial
          supply
          (occurrence :: occurrences)
          rest
  in
  add_initial supply [] initial_formulas

let find_occurrence state occurrence_id =
  List.find_opt
    (fun occurrence ->
      Nested_sequent.compare_occurrence_id
        occurrence.occurrence_id
        occurrence_id
      = 0)
    state.formulas

let formulas_at state position =
  List.filter
    (fun occurrence ->
      Nested_sequent.compare_position
        occurrence.position
        position
      = 0)
    state.formulas

let add_formula supply state position formula =
  if not (Nested_sequent.has_position state.tree position) then
    None
  else
    let occurrence_id, supply =
      Nested_sequent.fresh_occurrence_id supply
    in
    let occurrence =
      {
        occurrence_id;
        position;
        formula;
      }
    in
    Some
      ( { state with
          formulas = occurrence :: state.formulas;
        },
        occurrence,
        supply )

let remove_occurrence state occurrence_id =
  match find_occurrence state occurrence_id with
  | None ->
      None
  | Some _ ->
      Some
        {
          state with
          formulas =
            List.filter
              (fun occurrence ->
                Nested_sequent.compare_occurrence_id
                  occurrence.occurrence_id
                  occurrence_id
                <> 0)
              state.formulas;
        }

let add_empty_child supply state parent modality =
  match
    Nested_sequent.add_empty_child
      supply
      state.tree
      parent
      modality
  with
  | None ->
      None
  | Some (tree, child_position, supply) ->
      Some
        ( { state with tree },
          child_position,
          supply )

let positions state =
  Nested_sequent.position_ids state.tree

let has_position state position =
  Nested_sequent.has_position state.tree position

let equal left right =
  Nested_sequent.equal left.tree right.tree
  && List.length left.formulas = List.length right.formulas
  && List.for_all
       (fun occurrence ->
         match
           List.find_opt
             (fun other ->
               Nested_sequent.compare_occurrence_id
                 occurrence.occurrence_id
                 other.occurrence_id
               = 0)
             right.formulas
         with
         | None ->
             false
         | Some other ->
             Nested_sequent.compare_position
               occurrence.position
               other.position
             = 0
             && occurrence.formula = other.formula)
       left.formulas

let add_existing_formula
    state
    position
    occurrence_id
    formula =
  if
    not (has_position state position)
    || Option.is_some
         (find_occurrence state occurrence_id)
  then
    None
  else
    Some
      {
        state with
        formulas =
          {
            occurrence_id;
            position;
            formula;
          }
          :: state.formulas;
      }

let add_existing_empty_child
    state
    parent
    modality
    child_position =
  match
    Nested_sequent.add_existing_empty_child
      state.tree
      parent
      modality
      child_position
  with
  | None ->
      None
  | Some tree ->
      Some { state with tree }
