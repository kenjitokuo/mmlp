(** Reported answers.

    A computed answer is reported only when no answer reported before
    it has it as an output instance.  An answer [specific] is an output
    instance of [general] when some ordinary output substitution maps
    [general] to [specific] on every answer variable.  Ordinary output
    substitutions do not instantiate the free query variables outside
    the answer variables, so those variables are rigid in the test. *)

type answer =
  (string * Syntax.term) list

val rigid_variables :
  query:Syntax.formula ->
  answer_variables:string list ->
  Substitution.String_set.t
(** The free variables of the query that are not answer variables. *)

val output_instance :
  rigid:Substitution.String_set.t ->
  answer_variables:string list ->
  general:answer ->
  specific:answer ->
  bool
(** [output_instance ~rigid ~answer_variables ~general ~specific] decides
    whether [specific] is an output instance of [general].  An answer
    variable without a binding is mapped to itself. *)

val report :
  rigid:Substitution.String_set.t ->
  answer_variables:string list ->
  answer_of:('a -> answer) ->
  'a list ->
  'a list
(** Keep, in order, the items whose answers are not output instances of
    the answer of an item kept before them. *)
