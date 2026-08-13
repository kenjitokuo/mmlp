type t = {
  walk : Signed_walk.t;
  derivation : Grammar_derivation.t;
}

let valid
    ~grammar
    ~sequent
    ~modality
    ~source
    ~target
    certificate =
  Nested_sequent.compare_position certificate.walk.source source = 0
  && Nested_sequent.compare_position certificate.walk.target target = 0
  && Signed_walk.valid sequent certificate.walk
  && Grammar.compare_word
       certificate.derivation.start_word
       [Modal_symbol.Forward modality]
     = 0
  &&
  match Grammar_derivation.replay_in grammar certificate.derivation with
  | None -> false
  | Some final_word ->
      Grammar.compare_word final_word (Signed_walk.label certificate.walk) = 0
