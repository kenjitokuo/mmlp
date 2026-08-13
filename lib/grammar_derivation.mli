type application = {
  production : Grammar.production;
  prefix : Grammar.word;
  suffix : Grammar.word;
}

type t = {
  start_word : Grammar.word;
  applications : application list;
}

val apply_application :
  Grammar.word ->
  application ->
  Grammar.word option

val replay :
  t ->
  Grammar.word option

val replay_in :
  Grammar.Production_set.t ->
  t ->
  Grammar.word option
