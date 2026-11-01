type prepared = {
  root : Symbolic_root.t;
  answers : Trusted_answer.t Seq.t;
}

let prepare
    ~environment
    ~program
    ~query
    ~answer_variables =
  match
    Symbolic_root.create
      ~environment
      ~program
      ~query
      ~answer_variables
  with
  | Error message ->
      Error message
  | Ok root ->
      Ok
        {
          root;
          answers =
            Trusted_search.iterative_deepening
              ~environment
              ~root;
        }

let answers_within_depth
    ~environment
    ~program
    ~query
    ~answer_variables
    ~depth =
  match
    Symbolic_root.create
      ~environment
      ~program
      ~query
      ~answer_variables
  with
  | Error message ->
      Error message
  | Ok root ->
      Ok
        (Trusted_search.answers_within_depth
           ~environment
           ~root
           ~depth)

let answers_at_exact_depth
    ~environment
    ~program
    ~query
    ~answer_variables
    ~depth =
  match
    Symbolic_root.create
      ~environment
      ~program
      ~query
      ~answer_variables
  with
  | Error message ->
      Error message
  | Ok root ->
      Ok
        (Trusted_search.answers_at_exact_depth
           ~environment
           ~root
           ~depth)

let focused_answers_within_depth
    ~environment
    ~program
    ~query
    ~answer_variables
    ~depth =
  match
    Symbolic_root.create
      ~environment
      ~program
      ~query
      ~answer_variables
  with
  | Error message ->
      Error message
  | Ok root ->
      Ok
        (Focused_search.answers_within_depth
           ~environment
           ~root
           ~depth)

let focused_answers_at_exact_depth
    ~environment
    ~program
    ~query
    ~answer_variables
    ~depth =
  match
    Symbolic_root.create
      ~environment
      ~program
      ~query
      ~answer_variables
  with
  | Error message ->
      Error message
  | Ok root ->
      Ok
        (Focused_search.answers_at_exact_depth
           ~environment
           ~root
           ~depth)

let prepare_focused
    ~environment
    ~program
    ~query
    ~answer_variables =
  match
    Symbolic_root.create
      ~environment
      ~program
      ~query
      ~answer_variables
  with
  | Error message ->
      Error message
  | Ok root ->
      Ok
        {
          root;
          answers =
            Focused_search.iterative_deepening
              ~environment
              ~root;
        }

let instantiate_answer
    ~query
    ~answer_variables
    ~trusted
    ~substitution =
  Answer_instance.instantiate
    ~query
    ~answer_variables
    ~answer:trusted.Trusted_answer.answer
    ~substitution

(* Reported answers within a height bound.  The stages of iterative
   deepening are run in order, each stage enumerating every derivation
   of height at most its bound, and the computed answers are filtered
   by the reporting test in the order in which they are produced.  The
   result is therefore the initial segment of the reported answers
   determined by the stages up to [depth]. *)
let reported_within_depth
    ~stage
    ~environment
    ~program
    ~query
    ~answer_variables
    ~depth =
  let rec collect bound produced =
    if bound > depth then
      Ok (List.concat (List.rev produced))
    else
      match
        stage
          ~environment
          ~program
          ~query
          ~answer_variables
          ~depth:bound
      with
      | Error message ->
          Error message
      | Ok answers ->
          collect (bound + 1) (answers :: produced)
  in
  match collect 0 [] with
  | Error message ->
      Error message
  | Ok produced ->
      Ok
        (Answer_report.report
           ~rigid:
             (Answer_report.rigid_variables
                ~query
                ~answer_variables)
           ~answer_variables
           ~answer_of:(fun trusted -> trusted.Trusted_answer.answer)
           produced)

let reported_answers_within_depth =
  reported_within_depth ~stage:answers_within_depth

let focused_reported_answers_within_depth =
  reported_within_depth ~stage:focused_answers_within_depth
