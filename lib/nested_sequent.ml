type position = Position of int

type occurrence_id = Occurrence_id of int

type formula_occurrence = {
  occurrence_id : occurrence_id;
  formula : Syntax.core_formula;
}

type t = {
  position : position;
  formulas : formula_occurrence list;
  children : child list;
}

and child = {
  modality : Syntax.modal_index;
  subtree : t;
}

type supply = {
  next_position : int;
  next_occurrence : int;
}

let initial_supply = {
  next_position = 0;
  next_occurrence = 0;
}

let fresh_position supply =
  let position = Position supply.next_position in
  let supply =
    { supply with next_position = supply.next_position + 1 }
  in
  (position, supply)

let fresh_occurrence_id supply =
  let occurrence_id = Occurrence_id supply.next_occurrence in
  let supply =
    { supply with next_occurrence = supply.next_occurrence + 1 }
  in
  (occurrence_id, supply)

let fresh_formula_occurrence supply formula =
  let occurrence_id, supply = fresh_occurrence_id supply in
  ({ occurrence_id; formula }, supply)

let compare_position (Position i) (Position j) =
  Int.compare i j

let compare_occurrence_id (Occurrence_id i) (Occurrence_id j) =
  Int.compare i j

let rec has_edge sequent ~source ~modality ~target =
  List.exists
    (fun child ->
      (compare_position sequent.position source = 0
       && Syntax.compare_modal_index child.modality modality = 0
       && compare_position child.subtree.position target = 0)
      || has_edge child.subtree ~source ~modality ~target)
    sequent.children

let rec has_position sequent position =
  compare_position sequent.position position = 0
  || List.exists
       (fun child -> has_position child.subtree position)
       sequent.children

let rec find_component sequent position =
  if compare_position sequent.position position = 0 then
    Some sequent
  else
    let rec search = function
      | [] -> None
      | child :: rest ->
          match find_component child.subtree position with
          | Some component -> Some component
          | None -> search rest
    in
    search sequent.children

let rec update_component sequent position f =
  if compare_position sequent.position position = 0 then
    Some (f sequent)
  else
    let rec update_children prefix = function
      | [] ->
          None
      | child :: rest ->
          match update_component child.subtree position f with
          | Some subtree ->
              Some
                {
                  sequent with
                  children =
                    List.rev_append
                      prefix
                      ({ child with subtree } :: rest);
                }
          | None ->
              update_children (child :: prefix) rest
    in
    update_children [] sequent.children

let rec find_occurrence sequent occurrence_id =
  match
    List.find_opt
      (fun occurrence ->
        compare_occurrence_id
          occurrence.occurrence_id
          occurrence_id
        = 0)
      sequent.formulas
  with
  | Some occurrence ->
      Some (sequent.position, occurrence)
  | None ->
      let rec search = function
        | [] -> None
        | child :: rest ->
            match find_occurrence child.subtree occurrence_id with
            | Some result -> Some result
            | None -> search rest
      in
      search sequent.children

let remove_occurrence sequent occurrence_id =
  update_component
    sequent
    (match find_occurrence sequent occurrence_id with
     | Some (position, _) -> position
     | None -> sequent.position)
    (fun component ->
      {
        component with
        formulas =
          List.filter
            (fun occurrence ->
              compare_occurrence_id
                occurrence.occurrence_id
                occurrence_id
              <> 0)
            component.formulas;
      })
  |> function
     | Some updated
       when find_occurrence sequent occurrence_id <> None ->
         Some updated
     | _ ->
         None

let add_formula supply sequent position formula =
  let occurrence, supply =
    fresh_formula_occurrence supply formula
  in
  match
    update_component
      sequent
      position
      (fun component ->
        {
          component with
          formulas = occurrence :: component.formulas;
        })
  with
  | None ->
      None
  | Some sequent ->
      Some (sequent, occurrence, supply)

let add_empty_child supply sequent parent modality =
  let position, supply = fresh_position supply in
  let subtree =
    {
      position;
      formulas = [];
      children = [];
    }
  in
  let child =
    {
      modality;
      subtree;
    }
  in
  match
    update_component
      sequent
      parent
      (fun component ->
        {
          component with
          children = child :: component.children;
        })
  with
  | None ->
      None
  | Some sequent ->
      Some (sequent, position, supply)

let rec proof_params sequent =
  let here =
    List.fold_left
      (fun parameters occurrence ->
        Substitution.String_set.union
          parameters
          (Substitution.proof_params_core_formula occurrence.formula))
      Substitution.String_set.empty
      sequent.formulas
  in
  List.fold_left
    (fun parameters child ->
      Substitution.String_set.union
        parameters
        (proof_params child.subtree))
    here
    sequent.children

let occurrence_id_is_fresh sequent occurrence_id =
  match find_occurrence sequent occurrence_id with
  | None -> true
  | Some _ -> false

let position_is_fresh sequent position =
  not (has_position sequent position)

let rec equal a b =
  let occurrence_equal
      (left : formula_occurrence)
      (right : formula_occurrence) =
    compare_occurrence_id left.occurrence_id right.occurrence_id = 0
    && left.formula = right.formula
  in
  let child_equal (left : child) (right : child) =
    Syntax.compare_modal_index left.modality right.modality = 0
    && equal left.subtree right.subtree
  in
  compare_position a.position b.position = 0
  && List.length a.formulas = List.length b.formulas
  && List.for_all
       (fun occurrence ->
         List.exists (occurrence_equal occurrence) b.formulas)
       a.formulas
  && List.length a.children = List.length b.children
  && List.for_all
       (fun child ->
         List.exists (child_equal child) b.children)
       a.children

let rec occurrence_ids sequent =
  let here =
    List.map
      (fun occurrence -> occurrence.occurrence_id)
      sequent.formulas
  in
  List.fold_left
    (fun ids child ->
      ids @ occurrence_ids child.subtree)
    here
    sequent.children

let new_occurrence_ids ~before ~after =
  let before_ids = occurrence_ids before in
  List.filter
    (fun occurrence_id ->
      not
        (List.exists
           (fun old_id ->
             compare_occurrence_id occurrence_id old_id = 0)
           before_ids))
    (occurrence_ids after)

let occurrence_ids_unique sequent =
  let ids = occurrence_ids sequent in
  let rec check = function
    | [] -> true
    | id :: rest ->
        not
          (List.exists
             (fun other ->
               compare_occurrence_id id other = 0)
             rest)
        && check rest
  in
  check ids

let rec position_ids sequent =
  sequent.position
  ::
  List.concat_map
    (fun child -> position_ids child.subtree)
    sequent.children

let position_ids_unique sequent =
  let ids = position_ids sequent in
  let rec check = function
    | [] -> true
    | id :: rest ->
        not
          (List.exists
             (fun other ->
               compare_position id other = 0)
             rest)
        && check rest
  in
  check ids

let new_position_ids ~before ~after =
  let before_ids = position_ids before in
  List.filter
    (fun position ->
      not
        (List.exists
           (fun old_position ->
             compare_position position old_position = 0)
           before_ids))
    (position_ids after)

let add_existing_occurrence sequent position occurrence =
  if not (occurrence_id_is_fresh sequent occurrence.occurrence_id) then
    None
  else
    update_component
      sequent
      position
      (fun component ->
        {
          component with
          formulas = occurrence :: component.formulas;
        })

let add_existing_empty_child sequent parent modality position =
  if not (position_is_fresh sequent position) then
    None
  else
    let subtree =
      {
        position;
        formulas = [];
        children = [];
      }
    in
    let child =
      {
        modality;
        subtree;
      }
    in
    update_component
      sequent
      parent
      (fun component ->
        {
          component with
          children = child :: component.children;
        })

let position_number (Position i) =
  i

let occurrence_id_number (Occurrence_id i) =
  i
