let certify_derivation
    ~environment
    ~root
    derivation =
  match Symbolic_search.solve_derivation derivation with
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
      end

let answers_within_depth
    ~environment
    ~root
    ~depth =
  Symbolic_search.derivations_within_depth
    ~environment
    ~depth
    (Symbolic_search.of_root root)
  |> List.filter_map
       (certify_derivation
          ~environment
          ~root)

let answers_at_exact_depth
    ~environment
    ~root
    ~depth =
  Symbolic_search.derivations_within_depth
    ~environment
    ~depth
    (Symbolic_search.of_root root)
  |> List.filter
       (fun derivation ->
         Symbolic_derivation.height derivation = depth)
  |> List.filter_map
       (certify_derivation
          ~environment
          ~root)

let iterative_deepening
    ~environment
    ~root =
  let rec enumerate depth () =
    let current =
      answers_at_exact_depth
        ~environment
        ~root
        ~depth
    in
    Seq.append
      (List.to_seq current)
      (enumerate (depth + 1))
      ()
  in
  enumerate 0
