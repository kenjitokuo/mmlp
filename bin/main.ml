open Mmlp

let program_sources = ref []
let query_source = ref None
let answer_variables = ref []
let axiom_sources = ref []
let depth = ref 8
let max_modal_index = ref 1

let add_program source =
  program_sources := source :: !program_sources

let add_answer variable =
  answer_variables := variable :: !answer_variables

let add_axiom source =
  axiom_sources := source :: !axiom_sources

let specifications =
  [
    ( "--program",
      Arg.String add_program,
      "FORMULA  Add a program formula; may be repeated" );
    ( "--query",
      Arg.String (fun source -> query_source := Some source),
      "FORMULA  Query formula" );
    ( "--answer",
      Arg.String add_answer,
      "VARIABLE Answer-role variable; may be repeated" );
    ( "--axiom",
      Arg.String add_axiom,
      "AXIOM  Add modal axiom: D:i, T:i, I:i,j, B:i,j, 4:i,j,k, or 5:i,j,k" );
    ( "--depth",
      Arg.Set_int depth,
      "N  Maximum focused proof depth (default: 8)" );
    ( "--max-modal-index",
      Arg.Set_int max_modal_index,
      "N  Largest permitted modal index (default: 1)" );
  ]

let usage =
  "mmlp --query FORMULA [--program FORMULA ...] \
   [--answer VARIABLE ...] [--axiom AXIOM ...] \
   [--depth N] [--max-modal-index N]"

let fail message =
  prerr_endline ("mmlp: " ^ message);
  exit 2

let parse_formula source =
  match
    Parser.parse_formula
      ~max_modal_index:!max_modal_index
      source
  with
  | Ok formula ->
      formula
  | Error message ->
      fail
        ("parse error in `" ^ source ^ "`: " ^ message)

let bind_result result f =
  match result with
  | Ok value -> f value
  | Error message -> Error message

let rec add_term_signature signature = function
  | Syntax.Var _
  | Syntax.Param _ ->
      Ok signature

  | Syntax.Const name ->
      Signature.add_constant signature name

  | Syntax.Fun (name, arguments) ->
      bind_result
        (Signature.add_function
           signature
           name
           (List.length arguments))
        (fun signature ->
          List.fold_left
            (fun result argument ->
              bind_result
                result
                (fun signature ->
                  add_term_signature
                    signature
                    argument))
            (Ok signature)
            arguments)

let rec add_formula_signature signature = function
  | Syntax.Bottom ->
      Ok signature

  | Syntax.Atom (name, arguments) ->
      bind_result
        (Signature.add_predicate
           signature
           name
           (List.length arguments))
        (fun signature ->
          List.fold_left
            (fun result argument ->
              bind_result
                result
                (fun signature ->
                  add_term_signature
                    signature
                    argument))
            (Ok signature)
            arguments)

  | Syntax.Not formula
  | Syntax.Forall (_, formula)
  | Syntax.Exists (_, formula)
  | Syntax.Box (_, formula)
  | Syntax.Diamond (_, formula) ->
      add_formula_signature signature formula

  | Syntax.And (left, right)
  | Syntax.Or (left, right)
  | Syntax.Imp (left, right) ->
      bind_result
        (add_formula_signature signature left)
        (fun signature ->
          add_formula_signature signature right)

let build_signature formulas =
  List.fold_left
    (fun result formula ->
      bind_result
        result
        (fun signature ->
          add_formula_signature signature formula))
    (Ok Signature.empty)
    formulas

let modal_index index =
  match
    Syntax.make_modal_index
      ~max_index:!max_modal_index
      index
  with
  | Ok index ->
      index
  | Error message ->
      fail message

let parse_integer text =
  try int_of_string (String.trim text)
  with Failure _ ->
    fail ("invalid modal index: " ^ text)

let split_indices text =
  String.split_on_char ',' text
  |> List.map parse_integer

let parse_axiom source =
  match String.split_on_char ':' source with
  | [kind; indices] ->
      let kind =
        String.uppercase_ascii (String.trim kind)
      in
      begin
        match kind, split_indices indices with
        | "D", [i] ->
            Modal_axiom.D (modal_index i)

        | "T", [i] ->
            Modal_axiom.T (modal_index i)

        | "I", [i; j] ->
            Modal_axiom.I
              (modal_index i, modal_index j)

        | "B", [i; j] ->
            Modal_axiom.B
              (modal_index i, modal_index j)

        | "4", [i; j; k] ->
            Modal_axiom.Four
              (modal_index i,
               modal_index j,
               modal_index k)

        | "5", [i; j; k] ->
            Modal_axiom.Five
              (modal_index i,
               modal_index j,
               modal_index k)

        | _ ->
            fail
              ("invalid modal axiom `" ^ source
               ^ "`; expected D:i, T:i, I:i,j, B:i,j, 4:i,j,k, or 5:i,j,k")
      end

  | _ ->
      fail
        ("invalid modal axiom `" ^ source
         ^ "`; expected KIND:indices")

let build_axioms sources =
  List.fold_left
    (fun axioms source ->
      Modal_axiom.Set.add
        (parse_axiom source)
        axioms)
    Modal_axiom.Set.empty
    sources

let rec string_of_term = function
  | Syntax.Var name ->
      name
  | Syntax.Param name ->
      "$" ^ name
  | Syntax.Const name ->
      name
  | Syntax.Fun (name, arguments) ->
      name
      ^ "("
      ^ String.concat ", "
          (List.map string_of_term arguments)
      ^ ")"

let print_answer index answer =
  Printf.printf "answer %d:" index;
  begin
    match answer with
    | [] ->
        print_string " yes"
    | bindings ->
        List.iter
          (fun (variable, term) ->
            Printf.printf
              " %s = %s"
              variable
              (string_of_term term))
          bindings
  end;
  print_newline ()

let () =
  Arg.parse
    specifications
    (fun argument ->
      fail ("unexpected argument: " ^ argument))
    usage;

  if !depth < 0 then
    fail "--depth must be nonnegative";

  if !max_modal_index < 0 then
    fail "--max-modal-index must be nonnegative";

  let query =
    match !query_source with
    | None ->
        fail "missing required --query FORMULA"
    | Some source ->
        parse_formula source
  in

  let program =
    List.rev_map
      parse_formula
      !program_sources
  in

  let answer_variables =
    List.rev !answer_variables
  in

  let signature =
    match build_signature (query :: program) with
    | Ok signature ->
        signature
    | Error message ->
        fail message
  in

  let axioms =
    build_axioms (List.rev !axiom_sources)
  in

  let environment =
    match
      Environment.create
        ~max_modal_index:!max_modal_index
        ~signature
        ~axioms
    with
    | Ok environment ->
        environment
    | Error message ->
        fail message
  in

  match
    Execution.focused_answers_within_depth
      ~environment
      ~program
      ~query
      ~answer_variables
      ~depth:!depth
  with
  | Error message ->
      fail message

  | Ok [] ->
      print_endline "no answer within depth bound"

  | Ok answers ->
      List.iteri
        (fun index trusted ->
          print_answer
            (index + 1)
            trusted.Trusted_answer.answer)
        answers
