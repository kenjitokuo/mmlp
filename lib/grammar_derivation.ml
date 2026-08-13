type application = {
  production : Grammar.production;
  prefix : Grammar.word;
  suffix : Grammar.word;
}

type t = {
  start_word : Grammar.word;
  applications : application list;
}

let apply_application word application =
  let expected =
    application.prefix
    @ application.production.lhs
    @ application.suffix
  in
  if Grammar.compare_word word expected <> 0 then
    None
  else
    Some
      (application.prefix
       @ application.production.rhs
       @ application.suffix)

let replay derivation =
  List.fold_left
    (fun current application ->
      match current with
      | None -> None
      | Some word -> apply_application word application)
    (Some derivation.start_word)
    derivation.applications

let replay_in grammar derivation =
  List.fold_left
    (fun current application ->
      match current with
      | None -> None
      | Some word ->
          if
            not
              (Grammar.Production_set.mem
                 application.production
                 grammar)
          then
            None
          else
            apply_application word application)
    (Some derivation.start_word)
    derivation.applications
