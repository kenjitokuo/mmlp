type step = {
  source : Nested_sequent.position;
  label : Modal_symbol.t;
  target : Nested_sequent.position;
}

type t = {
  source : Nested_sequent.position;
  target : Nested_sequent.position;
  steps : step list;
}

let label walk =
  List.map (fun step -> step.label) walk.steps

let empty_at position =
  {
    source = position;
    target = position;
    steps = [];
  }

let valid_step sequent step =
  match step.label with
  | Modal_symbol.Forward i ->
      Nested_sequent.has_edge
        sequent
        ~source:step.source
        ~modality:i
        ~target:step.target
  | Modal_symbol.Backward i ->
      Nested_sequent.has_edge
        sequent
        ~source:step.target
        ~modality:i
        ~target:step.source

let valid sequent walk =
  if
    not (Nested_sequent.has_position sequent walk.source)
    || not (Nested_sequent.has_position sequent walk.target)
  then
    false
  else
    let rec check current = function
      | [] ->
          Nested_sequent.compare_position current walk.target = 0
      | (step : step) :: rest ->
          Nested_sequent.compare_position current step.source = 0
          && valid_step sequent step
          && check step.target rest
    in
    check walk.source walk.steps
