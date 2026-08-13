type t

val create :
  max_modal_index:int ->
  signature:Signature.t ->
  axioms:Modal_axiom.Set.t ->
  (t, string) result

val max_modal_index :
  t ->
  int

val signature :
  t ->
  Signature.t

val axioms :
  t ->
  Modal_axiom.Set.t

val make_modal_index :
  t ->
  int ->
  (Syntax.modal_index, string) result

val grammar :
  t ->
  Grammar.Production_set.t

val validate_surface_formula :
  t ->
  Syntax.formula ->
  (unit, string) result

val check_derivation :
  t ->
  Derivation.t ->
  bool
