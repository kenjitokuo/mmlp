val valid_state :
  Nested_sequent.t ->
  bool

val check_axiom_node :
  Derivation.t ->
  bool

val check_or_node :
  Derivation.t ->
  Nested_sequent.occurrence_id ->
  bool

val check_and_node :
  Derivation.t ->
  Nested_sequent.occurrence_id ->
  bool

val check_exists_node :
  Derivation.t ->
  Nested_sequent.occurrence_id ->
  Syntax.term ->
  bool

val check_forall_node :
  Derivation.t ->
  Nested_sequent.occurrence_id ->
  string ->
  bool

val check_box_node :
  Derivation.t ->
  Nested_sequent.occurrence_id ->
  Nested_sequent.position ->
  bool

val check_diamond_node :
  grammar:Grammar.Production_set.t ->
  Derivation.t ->
  Nested_sequent.occurrence_id ->
  Nested_sequent.position ->
  Modal_certificate.t ->
  bool

val check_seriality_node :
  axioms:Modal_axiom.Set.t ->
  Derivation.t ->
  Nested_sequent.position ->
  Syntax.modal_index ->
  Nested_sequent.position ->
  bool

val valid :
  signature:Signature.t ->
  axioms:Modal_axiom.Set.t ->
  Derivation.t ->
  bool
