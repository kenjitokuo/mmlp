type parse =
  | Stop of Signed_walk.step
  | Expand of Grammar.production * parse list

type fact = {
  symbol : Modal_symbol.t;
  source : Nested_sequent.position;
  target : Nested_sequent.position;
  parse : parse;
}

let same_fact_key left right =
  Modal_symbol.compare left.symbol right.symbol = 0
  && Nested_sequent.compare_position left.source right.source = 0
  && Nested_sequent.compare_position left.target right.target = 0

let add_fact fact facts =
  if List.exists (same_fact_key fact) facts then
    facts, false
  else
    fact :: facts, true

let rec tree_steps sequent =
  List.concat_map
    (fun child ->
      let forward =
        {
          Signed_walk.source = sequent.Nested_sequent.position;
          label = Modal_symbol.Forward child.Nested_sequent.modality;
          target = child.Nested_sequent.subtree.Nested_sequent.position;
        }
      in
      let backward =
        {
          Signed_walk.source = child.Nested_sequent.subtree.Nested_sequent.position;
          label = Modal_symbol.Backward child.Nested_sequent.modality;
          target = sequent.Nested_sequent.position;
        }
      in
      forward
      :: backward
      :: tree_steps child.Nested_sequent.subtree)
    sequent.Nested_sequent.children

let initial_facts sequent =
  List.map
    (fun step ->
      {
        symbol = step.Signed_walk.label;
        source = step.Signed_walk.source;
        target = step.Signed_walk.target;
        parse = Stop step;
      })
    (tree_steps sequent)

let facts_from facts symbol source =
  List.filter
    (fun fact ->
      Modal_symbol.compare fact.symbol symbol = 0
      && Nested_sequent.compare_position fact.source source = 0)
    facts

let rec derive_rhs facts rhs source =
  match rhs with
  | [] ->
      [source, []]
  | symbol :: rest ->
      List.concat_map
        (fun fact ->
          List.map
            (fun (target, parses) ->
              target, fact.parse :: parses)
            (derive_rhs facts rest fact.target))
        (facts_from facts symbol source)

let lhs_symbol production =
  match production.Grammar.lhs with
  | [symbol] ->
      Some symbol
  | _ ->
      None

let saturate grammar sequent =
  let productions =
    Grammar.Production_set.elements grammar
  in
  let positions =
    Nested_sequent.position_ids sequent
  in
  let rec loop facts =
    let facts, changed =
      List.fold_left
        (fun (facts, changed) production ->
          match lhs_symbol production with
          | None ->
              facts, changed
          | Some symbol ->
              List.fold_left
                (fun (facts, changed) source ->
                  List.fold_left
                    (fun (facts, changed) (target, parses) ->
                      let fact =
                        {
                          symbol;
                          source;
                          target;
                          parse =
                            Expand
                              (production, parses);
                        }
                      in
                      let facts, added =
                        add_fact fact facts
                      in
                      facts, changed || added)
                    (facts, changed)
                    (derive_rhs
                       facts
                       production.Grammar.rhs
                       source))
                (facts, changed)
                positions)
        (facts, false)
        productions
    in
    if changed then
      loop facts
    else
      facts
  in
  loop (initial_facts sequent)

let rec parse_steps = function
  | Stop step ->
      [step]
  | Expand (_, children) ->
      List.concat_map parse_steps children

let root_symbol = function
  | Stop step ->
      step.Signed_walk.label
  | Expand (production, _) ->
      begin
        match lhs_symbol production with
        | Some symbol ->
            symbol
        | None ->
            failwith "certificate parse has non-singleton lhs"
      end

let rec compile_parse parse prefix suffix =
  match parse with
  | Stop step ->
      [], [step.Signed_walk.label]

  | Expand (production, children) ->
      let first_application =
        {
          Grammar_derivation.production;
          prefix;
          suffix;
        }
      in
      let rec compile_children
          prefix_acc
          applications
          final_word
          remaining =
        match remaining with
        | [] ->
            applications, final_word
        | child :: rest ->
            let remaining_symbols =
              List.map root_symbol rest
            in
            let child_applications, child_word =
              compile_parse
                child
                prefix_acc
                (remaining_symbols @ suffix)
            in
            compile_children
              (prefix_acc @ child_word)
              (applications @ child_applications)
              (final_word @ child_word)
              rest
      in
      let child_applications, final_word =
        compile_children prefix [] [] children
      in
      first_application :: child_applications,
      final_word

let certificate_of_fact fact =
  let steps =
    parse_steps fact.parse
  in
  let applications, _ =
    compile_parse fact.parse [] []
  in
  {
    Modal_certificate.walk =
      {
        Signed_walk.source = fact.source;
        target = fact.target;
        steps;
      };
    derivation =
      {
        Grammar_derivation.start_word =
          [fact.symbol];
        applications;
      };
  }

let find
    ~grammar
    ~sequent
    ~modality
    ~source
    ~target =
  let start_symbol =
    Modal_symbol.Forward modality
  in
  let facts =
    saturate grammar sequent
  in
  match
    List.find_opt
      (fun fact ->
        Modal_symbol.compare
          fact.symbol
          start_symbol
        = 0
        && Nested_sequent.compare_position
             fact.source
             source
           = 0
        && Nested_sequent.compare_position
             fact.target
             target
           = 0)
      facts
  with
  | None ->
      None
  | Some fact ->
      let certificate =
        certificate_of_fact fact
      in
      if
        Modal_certificate.valid
          ~grammar
          ~sequent
          ~modality
          ~source
          ~target
          certificate
      then
        Some certificate
      else
        None
