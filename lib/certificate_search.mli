val find :
  grammar:Grammar.Production_set.t ->
  sequent:Nested_sequent.t ->
  modality:Syntax.modal_index ->
  source:Nested_sequent.position ->
  target:Nested_sequent.position ->
  Modal_certificate.t option
