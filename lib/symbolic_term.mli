type flexible_kind =
  | Answer of string
  | Witness
  | Auxiliary

type flexible_variable

type term =
  | Var of string
  | Param of string
  | Flex of flexible_variable
  | Const of string
  | Fun of string * term list

type supply

val initial_supply :
  supply

val fresh_answer :
  supply ->
  string ->
  flexible_variable * supply

val fresh_meta :
  supply ->
  active_eigenparameters:Substitution.String_set.t ->
  birth_node:int ->
  flexible_variable * supply

val fresh_restriction :
  supply ->
  permission:Substitution.String_set.t ->
  flexible_variable * supply

val compare_flexible :
  flexible_variable ->
  flexible_variable ->
  int

val equal_flexible :
  flexible_variable ->
  flexible_variable ->
  bool

val permission :
  flexible_variable ->
  Substitution.String_set.t

val kind :
  flexible_variable ->
  flexible_kind

val birth_node :
  flexible_variable ->
  int option

val proof_parameters :
  term ->
  Substitution.String_set.t

val flexible_variables :
  term ->
  flexible_variable list

val safe_for :
  flexible_variable ->
  term ->
  bool



val fresh_answer_with_permission :
  supply ->
  string ->
  permission:Substitution.String_set.t ->
  flexible_variable * supply

val fresh_auxiliary :
  supply ->
  permission:Substitution.String_set.t ->
  flexible_variable * supply


val supply_after :
  flexible_variable list ->
  supply
