type position

type occurrence_id

type formula_occurrence = {
  occurrence_id : occurrence_id;
  formula : Syntax.core_formula;
}

type t = {
  position : position;
  formulas : formula_occurrence list;
  children : child list;
}

and child = {
  modality : Syntax.modal_index;
  subtree : t;
}

type supply

val initial_supply : supply

val fresh_position :
  supply -> position * supply

val fresh_occurrence_id :
  supply -> occurrence_id * supply

val fresh_formula_occurrence :
  supply ->
  Syntax.core_formula ->
  formula_occurrence * supply

val compare_position : position -> position -> int

val compare_occurrence_id : occurrence_id -> occurrence_id -> int

val has_edge :
  t ->
  source:position ->
  modality:Syntax.modal_index ->
  target:position ->
  bool

val has_position :
  t ->
  position ->
  bool

val find_component :
  t ->
  position ->
  t option

val update_component :
  t ->
  position ->
  (t -> t) ->
  t option

val find_occurrence :
  t ->
  occurrence_id ->
  (position * formula_occurrence) option

val remove_occurrence :
  t ->
  occurrence_id ->
  t option

val add_formula :
  supply ->
  t ->
  position ->
  Syntax.core_formula ->
  (t * formula_occurrence * supply) option

val add_empty_child :
  supply ->
  t ->
  position ->
  Syntax.modal_index ->
  (t * position * supply) option

val proof_params :
  t ->
  Substitution.String_set.t

val occurrence_id_is_fresh :
  t ->
  occurrence_id ->
  bool

val position_is_fresh :
  t ->
  position ->
  bool

val equal :
  t ->
  t ->
  bool

val occurrence_ids :
  t ->
  occurrence_id list

val new_occurrence_ids :
  before:t ->
  after:t ->
  occurrence_id list

val occurrence_ids_unique :
  t ->
  bool

val position_ids :
  t ->
  position list

val position_ids_unique :
  t ->
  bool

val new_position_ids :
  before:t ->
  after:t ->
  position list

val add_existing_occurrence :
  t ->
  position ->
  formula_occurrence ->
  t option

val add_existing_empty_child :
  t ->
  position ->
  Syntax.modal_index ->
  position ->
  t option

val position_number :
  position ->
  int

val occurrence_id_number :
  occurrence_id ->
  int
