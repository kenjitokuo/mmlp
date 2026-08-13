open Mmlp

let fail message = failwith ("comprehensive test: " ^ message)

let get_ok = function
  | Ok value -> value
  | Error message -> fail message

let modality ~max_index index =
  get_ok (Syntax.make_modal_index ~max_index index)

let signature_p1_c =
  Signature.empty
  |> fun s -> get_ok (Signature.add_predicate s "p" 1)
  |> fun s -> get_ok (Signature.add_constant s "c")

let signature_p0 =
  get_ok (Signature.add_predicate Signature.empty "p" 0)

let environment ~max_modal_index ~signature ~axioms =
  get_ok
    (Environment.create
       ~max_modal_index
       ~signature
       ~axioms)

let has_answer expected answers =
  List.exists
    (fun trusted ->
      trusted.Trusted_answer.answer = expected)
    answers

(* Parser: term constructors and variable/constant distinction. *)
let () =
  match Parser.parse_term "f(X,a)" with
  | Ok
      (Syntax.Fun
         ("f",
          [Syntax.Var "X"; Syntax.Const "a"])) ->
      ()
  | Ok _ ->
      fail "parser produced the wrong term structure"
  | Error message ->
      fail message

(* Parser: implication must be right associative. *)
let () =
  match
    Parser.parse_formula
      ~max_modal_index:1
      "p(X) -> p(Y) -> p(Z)"
  with
  | Ok
      (Syntax.Imp
         ( Syntax.Atom ("p", [Syntax.Var "X"]),
           Syntax.Imp
             ( Syntax.Atom ("p", [Syntax.Var "Y"]),
               Syntax.Atom ("p", [Syntax.Var "Z"]) ) )) ->
      ()
  | Ok _ ->
      fail "implication was not parsed right-associatively"
  | Error message ->
      fail message

(* Parser: modal-index boundary. *)
let () =
  match
    Parser.parse_formula
      ~max_modal_index:1
      "box[2] p(X)"
  with
  | Error _ ->
      ()
  | Ok _ ->
      fail "parser admitted an out-of-range modal index"

(* NNF: negated implication becomes conjunction of antecedent and
   negative consequent. *)
let () =
  let p =
    Syntax.Atom ("p", [Syntax.Var "X"])
  in
  let q =
    Syntax.Atom ("q", [Syntax.Var "X"])
  in
  match
    Nnf.nnf_plus
      (Syntax.Not (Syntax.Imp (p, q)))
  with
  | Syntax.CoreAnd
      ( Syntax.PosAtom ("p", [Syntax.Var "X"]),
        Syntax.NegAtom ("q", [Syntax.Var "X"]) ) ->
      ()
  | _ ->
      fail "NNF translation of negated implication is incorrect"

(* Signature validation: arity mismatch must be rejected. *)
let () =
  match
    Signature.validate_formula
      signature_p1_c
      (Syntax.Atom
         ("p", [Syntax.Const "c"; Syntax.Const "c"]))
  with
  | Error _ ->
      ()
  | Ok () ->
      fail "signature validation admitted a predicate arity mismatch"

(* Symbolic root: answer roles must be free query variables. *)
let () =
  let env =
    environment
      ~max_modal_index:1
      ~signature:signature_p1_c
      ~axioms:Modal_axiom.Set.empty
  in
  match
    Symbolic_root.create
      ~environment:env
      ~program:[]
      ~query:(Syntax.Atom ("p", [Syntax.Const "c"]))
      ~answer_variables:["X"]
  with
  | Error _ ->
      ()
  | Ok _ ->
      fail "root admitted an answer variable not free in the query"

(* Scoped unification: ordinary binding succeeds. *)
let () =
  let empty =
    Substitution.String_set.empty
  in
  let x, supply =
    Symbolic_term.fresh_meta
      Symbolic_term.initial_supply
      ~active_eigenparameters:empty
      ~birth_node:0
  in
  match
    Scoped_unification.solve
      ~supply
      [ Symbolic_term.Flex x,
        Symbolic_term.Const "a" ]
  with
  | Scoped_unification.Unsolvable ->
      fail "scoped unification rejected an ordinary safe binding"
  | Scoped_unification.Solved (substitution, _) ->
      begin
        match
          Symbolic_substitution.apply
            substitution
            (Symbolic_term.Flex x)
        with
        | Symbolic_term.Const "a" ->
            ()
        | _ ->
            fail "scoped unification returned the wrong binding"
      end

(* Scoped unification: an eigenparameter outside permission is forbidden. *)
let () =
  let empty =
    Substitution.String_set.empty
  in
  let x, supply =
    Symbolic_term.fresh_meta
      Symbolic_term.initial_supply
      ~active_eigenparameters:empty
      ~birth_node:0
  in
  match
    Scoped_unification.solve
      ~supply
      [ Symbolic_term.Flex x,
        Symbolic_term.Param "a0" ]
  with
  | Scoped_unification.Unsolvable ->
      ()
  | Scoped_unification.Solved _ ->
      fail "scoped unification leaked a forbidden eigenparameter"

(* T: certificate search must find the empty self-walk. *)
let () =
  let i = modality ~max_index:1 1 in
  let axioms =
    Modal_axiom.Set.singleton (Modal_axiom.T i)
  in
  let env =
    environment
      ~max_modal_index:1
      ~signature:Signature.empty
      ~axioms
  in
  let root, _ =
    Nested_sequent.fresh_position
      Nested_sequent.initial_supply
  in
  let sequent =
    {
      Nested_sequent.position = root;
      formulas = [];
      children = [];
    }
  in
  match
    Certificate_search.find
      ~grammar:(Environment.grammar env)
      ~sequent
      ~modality:i
      ~source:root
      ~target:root
  with
  | None ->
      fail "T certificate search failed on the empty self-walk"
  | Some certificate ->
      assert
        (Modal_certificate.valid
           ~grammar:(Environment.grammar env)
           ~sequent
           ~modality:i
           ~source:root
           ~target:root
           certificate)

(* Without T, the corresponding self certificate must not exist. *)
let () =
  let i = modality ~max_index:1 1 in
  let env =
    environment
      ~max_modal_index:1
      ~signature:Signature.empty
      ~axioms:Modal_axiom.Set.empty
  in
  let root, _ =
    Nested_sequent.fresh_position
      Nested_sequent.initial_supply
  in
  let sequent =
    {
      Nested_sequent.position = root;
      formulas = [];
      children = [];
    }
  in
  match
    Certificate_search.find
      ~grammar:(Environment.grammar env)
      ~sequent
      ~modality:i
      ~source:root
      ~target:root
  with
  | None ->
      ()
  | Some _ ->
      fail "empty grammar unexpectedly yielded a T-like self certificate"

(* I_12: a direct 2-edge must be usable as modality 1 reachability. *)
let () =
  let i = modality ~max_index:2 1 in
  let j = modality ~max_index:2 2 in
  let axioms =
    Modal_axiom.Set.singleton (Modal_axiom.I (i, j))
  in
  let env =
    environment
      ~max_modal_index:2
      ~signature:Signature.empty
      ~axioms
  in
  let root, supply1 =
    Nested_sequent.fresh_position
      Nested_sequent.initial_supply
  in
  let initial =
    {
      Nested_sequent.position = root;
      formulas = [];
      children = [];
    }
  in
  let sequent, child, _ =
    match
      Nested_sequent.add_empty_child
        supply1 initial root j
    with
    | Some result -> result
    | None -> fail "could not create I-test child"
  in
  match
    Certificate_search.find
      ~grammar:(Environment.grammar env)
      ~sequent
      ~modality:i
      ~source:root
      ~target:child
  with
  | Some certificate ->
      assert
        (Modal_certificate.valid
           ~grammar:(Environment.grammar env)
           ~sequent
           ~modality:i
           ~source:root
           ~target:child
           certificate)
  | None ->
      fail "I_12 certificate reachability was not discovered"

(* 4_123: a 2-edge followed by a 3-edge must realize modality 1. *)
let () =
  let i = modality ~max_index:3 1 in
  let j = modality ~max_index:3 2 in
  let k = modality ~max_index:3 3 in
  let axioms =
    Modal_axiom.Set.singleton
      (Modal_axiom.Four (i, j, k))
  in
  let env =
    environment
      ~max_modal_index:3
      ~signature:Signature.empty
      ~axioms
  in
  let root, supply1 =
    Nested_sequent.fresh_position
      Nested_sequent.initial_supply
  in
  let initial =
    {
      Nested_sequent.position = root;
      formulas = [];
      children = [];
    }
  in
  let with_child, child, supply2 =
    match
      Nested_sequent.add_empty_child
        supply1 initial root j
    with
    | Some result -> result
    | None -> fail "could not create 4-test first child"
  in
  let sequent, grandchild, _ =
    match
      Nested_sequent.add_empty_child
        supply2 with_child child k
    with
    | Some result -> result
    | None -> fail "could not create 4-test second child"
  in
  match
    Certificate_search.find
      ~grammar:(Environment.grammar env)
      ~sequent
      ~modality:i
      ~source:root
      ~target:grandchild
  with
  | Some certificate ->
      assert
        (Modal_certificate.valid
           ~grammar:(Environment.grammar env)
           ~sequent
           ~modality:i
           ~source:root
           ~target:grandchild
           certificate)
  | None ->
      fail "4_123 certificate reachability was not discovered"

(* D: scheduler must expose a seriality obligation even without
   an existing child. *)
let () =
  let i = modality ~max_index:1 1 in
  let axioms =
    Modal_axiom.Set.singleton (Modal_axiom.D i)
  in
  let env =
    environment
      ~max_modal_index:1
      ~signature:Signature.empty
      ~axioms
  in
  let root, supply1 =
    Nested_sequent.fresh_position
      Nested_sequent.initial_supply
  in
  let bottom, _ =
    Nested_sequent.fresh_formula_occurrence
      supply1
      Syntax.CoreBottom
  in
  let sequent =
    {
      Nested_sequent.position = root;
      formulas = [bottom];
      children = [];
    }
  in
  let rec advance configuration =
    match
      Saturation_scheduler.step
        ~environment:env
        configuration
    with
    | Ok (Saturation_scheduler.Bookkeeping successor) ->
        advance successor
    | Ok
        (Saturation_scheduler.Applied
           {
             obligation =
               Saturation_scheduler.Seriality (m, p);
             _;
           }) ->
        assert
          (Syntax.compare_modal_index m i = 0
           && Nested_sequent.compare_position p root = 0)
    | Ok _ ->
        fail
          "scheduler applied an unexpected obligation before seriality"
    | Error message ->
        fail message
  in
  advance (Saturation_scheduler.create sequent)

(* Implicit universal closure of a free program variable must work
   operationally, not merely at root construction. *)
let () =
  let env =
    environment
      ~max_modal_index:1
      ~signature:signature_p1_c
      ~axioms:Modal_axiom.Set.empty
  in
  match
    Execution.answers_within_depth
      ~environment:env
      ~program:
        [Syntax.Atom ("p", [Syntax.Var "x"])]
      ~query:
        (Syntax.Atom ("p", [Syntax.Const "c"]))
      ~answer_variables:[]
      ~depth:3
  with
  | Error message ->
      fail message
  | Ok [] ->
      fail "universally closed free-variable program did not prove p(c)"
  | Ok answers ->
      List.iter
        (fun trusted ->
          assert
            (Environment.check_derivation
               env
               trusted.Trusted_answer.ordinary_derivation))
        answers

(* End-to-end first-order computed answer, unfocused and focused. *)
let () =
  let env =
    environment
      ~max_modal_index:1
      ~signature:signature_p1_c
      ~axioms:Modal_axiom.Set.empty
  in
  let program =
    [Syntax.Atom ("p", [Syntax.Const "c"])]
  in
  let query =
    Syntax.Atom ("p", [Syntax.Var "X"])
  in
  let expected =
    [("X", Syntax.Const "c")]
  in
  let unfocused =
    get_ok
      (Execution.answers_within_depth
         ~environment:env
         ~program
         ~query
         ~answer_variables:["X"]
         ~depth:4)
  in
  let focused =
    get_ok
      (Execution.focused_answers_within_depth
         ~environment:env
         ~program
         ~query
         ~answer_variables:["X"]
         ~depth:4)
  in
  if not (has_answer expected unfocused) then
    fail "unfocused execution failed to compute X = c";
  if not (has_answer expected focused) then
    fail "focused execution failed to compute X = c"

(* End-to-end modal T: Box_1 p entails p, and the successful trusted
   proof must pass the ordinary certificate checker. *)
let () =
  let i = modality ~max_index:1 1 in
  let axioms =
    Modal_axiom.Set.singleton (Modal_axiom.T i)
  in
  let env =
    environment
      ~max_modal_index:1
      ~signature:signature_p0
      ~axioms
  in
  let answers =
    get_ok
      (Execution.focused_answers_within_depth
         ~environment:env
         ~program:
           [Syntax.Box
              (i, Syntax.Atom ("p", []))]
         ~query:(Syntax.Atom ("p", []))
         ~answer_variables:[]
         ~depth:4)
  in
  match answers with
  | [] ->
      fail "focused T execution failed to derive Box_1 p -> p"
  | trusted :: _ ->
      assert
        (Environment.check_derivation
           env
           trusted.Trusted_answer.ordinary_derivation)
