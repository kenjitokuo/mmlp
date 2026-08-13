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
