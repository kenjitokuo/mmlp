open Mmlp

let signature_empty =
  Signature.empty

let signature_p0 =
  match Signature.add_predicate Signature.empty "p" 0 with
  | Ok signature -> signature
  | Error message -> failwith message

let signature_p1 =
  match Signature.add_predicate Signature.empty "p" 1 with
  | Ok signature -> signature
  | Error message -> failwith message

let signature_p1_c =
  match Signature.add_constant signature_p1 "c" with
  | Ok signature -> signature
  | Error message -> failwith message

let signature_p1_q1 =
  match Signature.add_predicate signature_p1 "q" 1 with
  | Ok signature -> signature
  | Error message -> failwith message
open Mmlp

let signature_p1_f1 =
  match Signature.add_function signature_p1 "f" 1 with
  | Ok signature -> signature
  | Error message -> failwith message
let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let top_occurrence, _supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      Syntax.CoreTop
  in
  let sequent =
    {
      Nested_sequent.position = root_position;
      formulas = [top_occurrence];
      children = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = sequent;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  assert
    (Proof_checker.valid
       ~signature:signature_empty
       ~axioms:Modal_axiom.Set.empty
       derivation)

let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let positive, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.PosAtom ("p", []))
  in
  let negative, _supply3 =
    Nested_sequent.fresh_formula_occurrence
      supply2
      (Syntax.NegAtom ("p", []))
  in
  let sequent =
    {
      Nested_sequent.position = root_position;
      formulas = [positive; negative];
      children = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = sequent;
      rule = Derivation.Atomic_axiom;
      premises = [];
    }
  in
  assert
    (Proof_checker.valid
       ~signature:signature_p0
       ~axioms:Modal_axiom.Set.empty
       derivation)

let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreOr
         (Syntax.PosAtom ("p", []),
          Syntax.NegAtom ("p", [])))
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [principal];
      children = [];
    }
  in
  let base =
    match
      Nested_sequent.remove_occurrence
        conclusion
        principal.Nested_sequent.occurrence_id
    with
    | Some state -> state
    | None -> failwith "failed to remove Or principal"
  in
  let premise_state1, _positive, supply3 =
    match
      Nested_sequent.add_formula
        supply2
        base
        root_position
        (Syntax.PosAtom ("p", []))
    with
    | Some result -> result
    | None -> failwith "failed to add positive atom"
  in
  let premise_state, _negative, _supply4 =
    match
      Nested_sequent.add_formula
        supply3
        premise_state1
        root_position
        (Syntax.NegAtom ("p", []))
    with
    | Some result -> result
    | None -> failwith "failed to add negative atom"
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Atomic_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Or
          principal.Nested_sequent.occurrence_id;
      premises = [premise];
    }
  in
  assert
    (Proof_checker.valid
       ~signature:signature_p0
       ~axioms:Modal_axiom.Set.empty
       derivation)

let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let disjunction =
    Syntax.CoreOr
      (Syntax.PosAtom ("p", []),
       Syntax.NegAtom ("p", []))
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreAnd (disjunction, disjunction))
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [principal];
      children = [];
    }
  in
  let make_or_branch supply =
    let base =
      match
        Nested_sequent.remove_occurrence
          conclusion
          principal.Nested_sequent.occurrence_id
      with
      | Some state -> state
      | None -> failwith "failed to remove And principal"
    in
    let or_occurrence, supply' =
      Nested_sequent.fresh_formula_occurrence
        supply
        disjunction
    in
    let and_premise_state =
      match
        Nested_sequent.add_existing_occurrence
          base
          root_position
          or_occurrence
      with
      | Some state -> state
      | None -> failwith "failed to add Or occurrence"
    in
    let or_base =
      match
        Nested_sequent.remove_occurrence
          and_premise_state
          or_occurrence.Nested_sequent.occurrence_id
      with
      | Some state -> state
      | None -> failwith "failed to remove Or principal"
    in
    let atomic_state1, _positive, supply'' =
      match
        Nested_sequent.add_formula
          supply'
          or_base
          root_position
          (Syntax.PosAtom ("p", []))
      with
      | Some result -> result
      | None -> failwith "failed to add positive atom"
    in
    let atomic_state, _negative, supply''' =
      match
        Nested_sequent.add_formula
          supply''
          atomic_state1
          root_position
          (Syntax.NegAtom ("p", []))
      with
      | Some result -> result
      | None -> failwith "failed to add negative atom"
    in
    let atomic_derivation =
      {
        Derivation.conclusion = atomic_state;
        rule = Derivation.Atomic_axiom;
        premises = [];
      }
    in
    let or_derivation =
      {
        Derivation.conclusion = and_premise_state;
        rule =
          Derivation.Or
            or_occurrence.Nested_sequent.occurrence_id;
        premises = [atomic_derivation];
      }
    in
    (or_derivation, supply''')
  in
  let branch1, supply3 = make_or_branch supply2 in
  let branch2, _supply4 = make_or_branch supply3 in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.And
          principal.Nested_sequent.occurrence_id;
      premises = [branch1; branch2];
    }
  in
  assert
    (Proof_checker.valid
       ~signature:signature_p0
       ~axioms:Modal_axiom.Set.empty
       derivation)

let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let body =
    Syntax.PosAtom ("p", [Syntax.Var "x"])
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreExists ("x", body))
  in
  let negative, supply3 =
    Nested_sequent.fresh_formula_occurrence
      supply2
      (Syntax.NegAtom ("p", [Syntax.Const "c"]))
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [principal; negative];
      children = [];
    }
  in
  let witness = Syntax.Const "c" in
  let instantiated =
    Syntax.PosAtom ("p", [Syntax.Const "c"])
  in
  let premise_state, _witness_occurrence, _supply4 =
    match
      Nested_sequent.add_formula
        supply3
        conclusion
        root_position
        instantiated
    with
    | Some result -> result
    | None -> failwith "failed to add existential witness instance"
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Atomic_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Exists
          (principal.Nested_sequent.occurrence_id, witness);
      premises = [premise];
    }
  in
  assert
    (Proof_checker.valid
       ~signature:signature_p1_c
       ~axioms:Modal_axiom.Set.empty
       derivation)

let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let body =
    Syntax.PosAtom ("p", [Syntax.Var "x"])
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreForall ("x", body))
  in
  let top_occurrence, supply3 =
    Nested_sequent.fresh_formula_occurrence
      supply2
      Syntax.CoreTop
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [principal; top_occurrence];
      children = [];
    }
  in
  let base =
    match
      Nested_sequent.remove_occurrence
        conclusion
        principal.Nested_sequent.occurrence_id
    with
    | Some state -> state
    | None -> failwith "failed to remove Forall principal"
  in
  let premise_state, _body_occurrence, _supply4 =
    match
      Nested_sequent.add_formula
        supply3
        base
        root_position
        (Syntax.PosAtom ("p", [Syntax.Param "a"]))
    with
    | Some result -> result
    | None -> failwith "failed to add universal instance"
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Forall
          (principal.Nested_sequent.occurrence_id, "a");
      premises = [premise];
    }
  in
  assert
    (Proof_checker.valid
       ~signature:signature_p1
       ~axioms:Modal_axiom.Set.empty
       derivation)

let () =
  let modality =
    match Syntax.make_modal_index ~max_index:1 1 with
    | Ok index -> index
    | Error message -> failwith message
  in
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreBox (modality, Syntax.CoreTop))
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [principal];
      children = [];
    }
  in
  let base =
    match
      Nested_sequent.remove_occurrence
        conclusion
        principal.Nested_sequent.occurrence_id
    with
    | Some state -> state
    | None -> failwith "failed to remove Box principal"
  in
  let with_child, child_position, supply3 =
    match
      Nested_sequent.add_empty_child
        supply2
        base
        root_position
        modality
    with
    | Some result -> result
    | None -> failwith "failed to add Box child"
  in
  let premise_state, _body_occurrence, _supply4 =
    match
      Nested_sequent.add_formula
        supply3
        with_child
        child_position
        Syntax.CoreTop
    with
    | Some result -> result
    | None -> failwith "failed to add Box body"
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Box
          (principal.Nested_sequent.occurrence_id,
           child_position);
      premises = [premise];
    }
  in
  assert
    (Proof_checker.valid
       ~signature:signature_empty
       ~axioms:Modal_axiom.Set.empty
       derivation)

let () =
  let modality =
    match Syntax.make_modal_index ~max_index:1 1 with
    | Ok index -> index
    | Error message -> failwith message
  in
  let t_axiom = Modal_axiom.T modality in
  let axioms = Modal_axiom.Set.singleton t_axiom in
  let production =
    match Grammar.base_production_of_axiom t_axiom with
    | Some production -> production
    | None -> failwith "T axiom produced no grammar production"
  in
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreDiamond (modality, Syntax.CoreTop))
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [principal];
      children = [];
    }
  in
  let premise_state, _body_occurrence, _supply3 =
    match
      Nested_sequent.add_formula
        supply2
        conclusion
        root_position
        Syntax.CoreTop
    with
    | Some result -> result
    | None -> failwith "failed to add Diamond body"
  in
  let walk =
    Signed_walk.empty_at root_position
  in
  let grammar_derivation =
    {
      Grammar_derivation.start_word = production.Grammar.lhs;
      applications =
        [
          {
            Grammar_derivation.production = production;
            prefix = [];
            suffix = [];
          };
        ];
    }
  in
  let certificate =
    {
      Modal_certificate.walk = walk;
      derivation = grammar_derivation;
    }
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Diamond
          (principal.Nested_sequent.occurrence_id,
           root_position,
           certificate);
      premises = [premise];
    }
  in
  assert
    (Proof_checker.valid
       ~signature:signature_empty
       ~axioms
       derivation)

let () =
  let modality =
    match Syntax.make_modal_index ~max_index:1 1 with
    | Ok index -> index
    | Error message -> failwith message
  in
  let axioms =
    Modal_axiom.Set.singleton (Modal_axiom.D modality)
  in
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let top_occurrence, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      Syntax.CoreTop
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [top_occurrence];
      children = [];
    }
  in
  let premise_state, child_position, _supply3 =
    match
      Nested_sequent.add_empty_child
        supply2
        conclusion
        root_position
        modality
    with
    | Some result -> result
    | None -> failwith "failed to add seriality child"
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Seriality
          (root_position, modality, child_position);
      premises = [premise];
    }
  in
  assert
    (Proof_checker.valid
       ~signature:signature_empty
       ~axioms
       derivation)

let () =
  let modality =
    match Syntax.make_modal_index ~max_index:1 1 with
    | Ok index -> index
    | Error message -> failwith message
  in
  let t_axiom = Modal_axiom.T modality in
  let production =
    match Grammar.base_production_of_axiom t_axiom with
    | Some production -> production
    | None -> failwith "T axiom produced no grammar production"
  in
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreDiamond (modality, Syntax.CoreTop))
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [principal];
      children = [];
    }
  in
  let premise_state, _body_occurrence, _supply3 =
    match
      Nested_sequent.add_formula
        supply2
        conclusion
        root_position
        Syntax.CoreTop
    with
    | Some result -> result
    | None -> failwith "failed to add Diamond body"
  in
  let certificate =
    {
      Modal_certificate.walk =
        Signed_walk.empty_at root_position;
      derivation =
        {
          Grammar_derivation.start_word = production.Grammar.lhs;
          applications =
            [
              {
                Grammar_derivation.production = production;
                prefix = [];
                suffix = [];
              };
            ];
        };
    }
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Diamond
          (principal.Nested_sequent.occurrence_id,
           root_position,
           certificate);
      premises = [premise];
    }
  in
  assert
    (not
       (Proof_checker.valid
          ~signature:signature_empty
          ~axioms:Modal_axiom.Set.empty
          derivation))


let () =
  let modality =
    match Syntax.make_modal_index ~max_index:1 1 with
    | Ok index -> index
    | Error message -> failwith message
  in
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let top_occurrence, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      Syntax.CoreTop
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [top_occurrence];
      children = [];
    }
  in
  let premise_state, child_position, _supply3 =
    match
      Nested_sequent.add_empty_child
        supply2
        conclusion
        root_position
        modality
    with
    | Some result -> result
    | None -> failwith "failed to add seriality child"
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Seriality
          (root_position, modality, child_position);
      premises = [premise];
    }
  in
  assert
    (not
       (Proof_checker.valid
          ~signature:signature_empty
          ~axioms:Modal_axiom.Set.empty
          derivation))

let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let body =
    Syntax.PosAtom ("p", [Syntax.Var "x"])
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreForall ("x", body))
  in
  let existing_parameter, supply3 =
    Nested_sequent.fresh_formula_occurrence
      supply2
      (Syntax.PosAtom ("q", [Syntax.Param "a"]))
  in
  let top_occurrence, supply4 =
    Nested_sequent.fresh_formula_occurrence
      supply3
      Syntax.CoreTop
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas =
        [principal; existing_parameter; top_occurrence];
      children = [];
    }
  in
  let base =
    match
      Nested_sequent.remove_occurrence
        conclusion
        principal.Nested_sequent.occurrence_id
    with
    | Some state -> state
    | None -> failwith "failed to remove Forall principal"
  in
  let premise_state, _body_occurrence, _supply5 =
    match
      Nested_sequent.add_formula
        supply4
        base
        root_position
        (Syntax.PosAtom ("p", [Syntax.Param "a"]))
    with
    | Some result -> result
    | None -> failwith "failed to add universal instance"
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Forall
          (principal.Nested_sequent.occurrence_id, "a");
      premises = [premise];
    }
  in
  assert
    (not
       (Proof_checker.valid
          ~signature:signature_p1_q1
          ~axioms:Modal_axiom.Set.empty
          derivation))

let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let top_occurrence, _supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      Syntax.CoreTop
  in
  let invalid_sequent =
    {
      Nested_sequent.position = root_position;
      formulas = [top_occurrence; top_occurrence];
      children = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = invalid_sequent;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  assert
    (not
       (Proof_checker.valid
          ~signature:signature_empty
          ~axioms:Modal_axiom.Set.empty
          derivation))

let () =
  let modality =
    match Syntax.make_modal_index ~max_index:1 1 with
    | Ok index -> index
    | Error message -> failwith message
  in
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let child_position, supply2 =
    Nested_sequent.fresh_position supply1
  in
  let top_occurrence, _supply3 =
    Nested_sequent.fresh_formula_occurrence
      supply2
      Syntax.CoreTop
  in
  let child =
    {
      Nested_sequent.position = child_position;
      formulas = [];
      children = [];
    }
  in
  let invalid_sequent =
    {
      Nested_sequent.position = root_position;
      formulas = [top_occurrence];
      children =
        [
          { Nested_sequent.modality = modality; subtree = child };
          { Nested_sequent.modality = modality; subtree = child };
        ];
    }
  in
  let derivation =
    {
      Derivation.conclusion = invalid_sequent;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  assert
    (not
       (Proof_checker.valid
          ~signature:signature_empty
          ~axioms:Modal_axiom.Set.empty
          derivation))



let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let positive, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.PosAtom ("p", []))
  in
  let negative, _supply3 =
    Nested_sequent.fresh_formula_occurrence
      supply2
      (Syntax.NegAtom ("p", []))
  in
  let sequent =
    {
      Nested_sequent.position = root_position;
      formulas = [positive; negative];
      children = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = sequent;
      rule = Derivation.Atomic_axiom;
      premises = [];
    }
  in
  assert
    (not
       (Proof_checker.valid
          ~signature:signature_empty
          ~axioms:Modal_axiom.Set.empty
          derivation))

let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreExists ("x", Syntax.CoreTop))
  in
  let conclusion =
    {
      Nested_sequent.position = root_position;
      formulas = [principal];
      children = [];
    }
  in
  let base =
    match
      Nested_sequent.remove_occurrence
        conclusion
        principal.Nested_sequent.occurrence_id
    with
    | Some state -> state
    | None -> failwith "failed to remove Exists principal"
  in
  let premise_state, _top_occurrence, _supply3 =
    match
      Nested_sequent.add_formula
        supply2
        base
        root_position
        Syntax.CoreTop
    with
    | Some result -> result
    | None -> failwith "failed to add existential instance"
  in
  let premise =
    {
      Derivation.conclusion = premise_state;
      rule = Derivation.Truth_axiom;
      premises = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = conclusion;
      rule =
        Derivation.Exists
          (principal.Nested_sequent.occurrence_id,
           Syntax.Const "undeclared");
      premises = [premise];
    }
  in
  assert
    (not
       (Proof_checker.valid
          ~signature:signature_empty
          ~axioms:Modal_axiom.Set.empty
          derivation))

let () =
  let supply0 = Nested_sequent.initial_supply in
  let root_position, supply1 =
    Nested_sequent.fresh_position supply0
  in
  let positive, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.PosAtom ("p", []))
  in
  let negative, _supply3 =
    Nested_sequent.fresh_formula_occurrence
      supply2
      (Syntax.NegAtom ("p", []))
  in
  let sequent =
    {
      Nested_sequent.position = root_position;
      formulas = [positive; negative];
      children = [];
    }
  in
  let derivation =
    {
      Derivation.conclusion = sequent;
      rule = Derivation.Atomic_axiom;
      premises = [];
    }
  in
  assert
    (not
       (Proof_checker.valid
          ~signature:signature_p1
          ~axioms:Modal_axiom.Set.empty
          derivation))


let () =
  let empty_permission =
    Substitution.String_set.empty
  in
  let x, supply1 =
    Symbolic_term.fresh_meta
      Symbolic_term.initial_supply
      ~active_eigenparameters:empty_permission
      ~birth_node:0
  in
  let y, _supply2 =
    Symbolic_term.fresh_meta
      supply1
      ~active_eigenparameters:empty_permission
      ~birth_node:0
  in
  let theta =
    match
      Symbolic_substitution.bind
        Symbolic_substitution.empty
        x
        (Symbolic_term.Flex y)
    with
    | Some substitution -> substitution
    | None -> failwith "failed to construct theta"
  in
  let gamma =
    match
      Symbolic_substitution.bind
        Symbolic_substitution.empty
        y
        (Symbolic_term.Const "a")
    with
    | Some substitution -> substitution
    | None -> failwith "failed to construct gamma"
  in
  match
    Symbolic_substitution.apply_postfix
      theta
      gamma
      (Symbolic_term.Flex x)
  with
  | Symbolic_term.Const "a" -> ()
  | _ -> failwith "postfix substitution order is incorrect"

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment ->
        environment
    | Error message ->
        failwith message
  in
  let root =
    match
      Symbolic_root.create
        ~environment
        ~program:[]
        ~query:(Syntax.Not Syntax.Bottom)
        ~answer_variables:[]
    with
    | Ok root ->
        root
    | Error message ->
        failwith message
  in
  match
    Trusted_search.answers_at_exact_depth
      ~environment
      ~root
      ~depth:0
  with
  | [trusted] ->
      begin
        match
          trusted.Trusted_answer.ordinary_derivation.Derivation.rule
        with
        | Derivation.Truth_axiom ->
            assert
              (Environment.check_derivation
                 environment
                 trusted.Trusted_answer.ordinary_derivation)
        | _ ->
            failwith
              "trusted search reconstructed the wrong ordinary rule"
      end
  | _ ->
      failwith
        "trusted search failed to produce exactly one depth-zero truth answer"

let () =
  let permission =
    Substitution.String_set.empty
  in
  let x, supply1 =
    Symbolic_term.fresh_meta
      Symbolic_term.initial_supply
      ~active_eigenparameters:permission
      ~birth_node:0
  in
  let y, _supply2 =
    Symbolic_term.fresh_meta
      supply1
      ~active_eigenparameters:permission
      ~birth_node:0
  in
  let mu =
    match
      Symbolic_substitution.bind
        Symbolic_substitution.empty
        x
        (Symbolic_term.Flex y)
    with
    | Some substitution -> substitution
    | None -> failwith "failed to construct opposite-alias mu"
  in
  let gamma =
    match
      Symbolic_substitution.bind
        Symbolic_substitution.empty
        y
        (Symbolic_term.Flex x)
    with
    | Some substitution -> substitution
    | None -> failwith "failed to construct opposite-alias gamma"
  in
  match
    Symbolic_substitution.apply_postfix
      mu
      gamma
      (Symbolic_term.Flex x)
  with
  | Symbolic_term.Flex flexible
    when Symbolic_term.equal_flexible flexible x ->
      ()
  | _ ->
      failwith
        "opposite-alias factorization was not evaluated extensionally"

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment ->
        environment
    | Error message ->
        failwith message
  in
  match
    Execution.answers_at_exact_depth
      ~environment
      ~program:[]
      ~query:(Syntax.Not Syntax.Bottom)
      ~answer_variables:[]
      ~depth:0
  with
  | Error message ->
      failwith message
  | Ok [trusted] ->
      assert
        (trusted.Trusted_answer.answer = []);
      assert
        (Environment.check_derivation
           environment
           trusted.Trusted_answer.ordinary_derivation)
  | Ok _ ->
      failwith
        "Execution API failed to return exactly one trusted depth-zero answer"

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment ->
        environment
    | Error message ->
        failwith message
  in
  match
    Execution.focused_answers_at_exact_depth
      ~environment
      ~program:[]
      ~query:
        (Syntax.Exists
           ("x", Syntax.Not Syntax.Bottom))
      ~answer_variables:[]
      ~depth:1
  with
  | Error message ->
      failwith message
  | Ok [] ->
      failwith
        "focused existential search produced no trusted depth-one answer"
  | Ok answers ->
      List.iter
        (fun trusted ->
          assert
            (Environment.check_derivation
               environment
               trusted.Trusted_answer.ordinary_derivation))
        answers

let () =
  let query =
    Syntax.Atom
      ("p",
       [Syntax.Var "X";
        Syntax.Var "Y"])
  in
  let answer =
    [("X", Syntax.Var "Z")]
  in
  match
    Answer_instance.instantiate
      ~query
      ~answer_variables:["X"]
      ~answer
      ~substitution:[("Y", Syntax.Const "a")]
  with
  | Error _ ->
      ()
  | Ok _ ->
      failwith
        "Answer_instance allowed instantiation of an original non-answer query variable"

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment ->
        environment
    | Error message ->
        failwith message
  in
  let root =
    match
      Symbolic_root.create
        ~environment
        ~program:[]
        ~query:(Syntax.Not Syntax.Bottom)
        ~answer_variables:[]
    with
    | Ok root ->
        root
    | Error message ->
        failwith message
  in
  let state =
    Symbolic_root.state root
  in
  let occurrence_id =
    match Symbolic_state.formulas state with
    | occurrence :: _ ->
        occurrence.Symbolic_state.occurrence_id
    | [] ->
        failwith
          "expected a symbolic root occurrence"
  in
  let universal parameter node_id =
    Symbolic_derivation.make
      ~node_id
      ~conclusion:state
      ~rule:
        (Symbolic_derivation.Forall
           (occurrence_id, parameter))
      ~premises:[]
  in
  let duplicate =
    Symbolic_derivation.make
      ~node_id:0
      ~conclusion:state
      ~rule:(Symbolic_derivation.And occurrence_id)
      ~premises:
        [ universal "a17" 1;
          universal "a17" 2 ]
  in
  assert
    (not
       (Symbolic_derivation.check_global_eigenparameters
          duplicate));
  let noncanonical_fresh =
    Symbolic_derivation.make
      ~node_id:0
      ~conclusion:state
      ~rule:(Symbolic_derivation.And occurrence_id)
      ~premises:
        [ universal "b37" 1;
          universal "q91" 2 ]
  in
  assert
    (Symbolic_derivation.check_global_eigenparameters
       noncanonical_fresh)

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment ->
        environment
    | Error message ->
        failwith message
  in
  let root =
    match
      Symbolic_root.create
        ~environment
        ~program:[]
        ~query:
          (Syntax.And
             ( Syntax.Forall
                 ("x", Syntax.Not Syntax.Bottom),
               Syntax.Forall
                 ("y", Syntax.Not Syntax.Bottom) ))
        ~answer_variables:[]
    with
    | Ok root ->
        root
    | Error message ->
        failwith message
  in
  let rec forall_parameters derivation =
    let local =
      match Symbolic_derivation.rule derivation with
      | Symbolic_derivation.Forall (_, parameter) ->
          [parameter]
      | _ ->
          []
    in
    local
    @ List.concat_map
        forall_parameters
        (Symbolic_derivation.premises derivation)
  in
  let derivations =
    Symbolic_search.derivations_within_depth
      ~environment
      ~depth:2
      (Symbolic_search.of_root root)
  in
  match
    List.find_opt
      (fun derivation ->
        List.length
          (forall_parameters derivation)
        = 2)
      derivations
  with
  | None ->
      failwith
        "reference search produced no two-universal conjunction derivation"
  | Some derivation ->
      assert
        (forall_parameters derivation
         = ["a0"; "a1"])

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment ->
        environment
    | Error message ->
        failwith message
  in
  let root =
    match
      Symbolic_root.create
        ~environment
        ~program:[]
        ~query:
          (Syntax.And
             ( Syntax.Forall
                 ("x", Syntax.Not Syntax.Bottom),
               Syntax.Forall
                 ("y", Syntax.Not Syntax.Bottom) ))
        ~answer_variables:[]
    with
    | Ok root ->
        root
    | Error message ->
        failwith message
  in
  let rec forall_parameters derivation =
    let local =
      match Symbolic_derivation.rule derivation with
      | Symbolic_derivation.Forall (_, parameter) ->
          [parameter]
      | _ ->
          []
    in
    local
    @ List.concat_map
        forall_parameters
        (Symbolic_derivation.premises derivation)
  in
  let derivations =
    Focused_search.derivations_within_depth
      ~environment
      ~depth:2
      (Symbolic_search.of_root root)
  in
  match
    List.find_opt
      (fun derivation ->
        List.length
          (forall_parameters derivation)
        = 2)
      derivations
  with
  | None ->
      failwith
        "focused reference search produced no two-universal conjunction derivation"
  | Some derivation ->
      assert
        (forall_parameters derivation
         = ["a0"; "a1"])

let () =
  let modality =
    match Syntax.make_modal_index ~max_index:1 1 with
    | Ok modality ->
        modality
    | Error message ->
        failwith message
  in
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment ->
        environment
    | Error message ->
        failwith message
  in
  let root =
    match
      Symbolic_root.create
        ~environment
        ~program:[]
        ~query:
          (Syntax.And
             ( Syntax.Box
                 (modality, Syntax.Not Syntax.Bottom),
               Syntax.Box
                 (modality, Syntax.Not Syntax.Bottom) ))
        ~answer_variables:[]
    with
    | Ok root ->
        root
    | Error message ->
        failwith message
  in
  let rec box_positions derivation =
    let local =
      match Symbolic_derivation.rule derivation with
      | Symbolic_derivation.Box (_, position) ->
          [position]
      | _ ->
          []
    in
    local
    @ List.concat_map
        box_positions
        (Symbolic_derivation.premises derivation)
  in
  let derivations =
    Focused_search.derivations_within_depth
      ~environment
      ~depth:2
      (Symbolic_search.of_root root)
  in
  match
    List.find_opt
      (fun derivation ->
        List.length (box_positions derivation) = 2)
      derivations
  with
  | None ->
      failwith
        "focused reference search produced no two-box conjunction derivation"
  | Some derivation ->
      begin
        match box_positions derivation with
        | [left_position; right_position] ->
            assert
              (Nested_sequent.compare_position
                 left_position
                 right_position
               <> 0)
        | _ ->
            assert false
      end

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment ->
        environment
    | Error message ->
        failwith message
  in
  let root =
    match
      Symbolic_root.create
        ~environment
        ~program:[]
        ~query:
          (Syntax.And
             ( Syntax.Exists
                 ("x", Syntax.Not Syntax.Bottom),
               Syntax.Exists
                 ("y", Syntax.Not Syntax.Bottom) ))
        ~answer_variables:[]
    with
    | Ok root ->
        root
    | Error message ->
        failwith message
  in
  let rec witnesses derivation =
    let local =
      match Symbolic_derivation.rule derivation with
      | Symbolic_derivation.Exists (_, witness) ->
          [witness]
      | _ ->
          []
    in
    local
    @ List.concat_map
        witnesses
        (Symbolic_derivation.premises derivation)
  in
  let derivations =
    Focused_search.derivations_within_depth
      ~environment
      ~depth:2
      (Symbolic_search.of_root root)
  in
  match
    List.find_opt
      (fun derivation ->
        List.length (witnesses derivation) = 2)
      derivations
  with
  | None ->
      failwith
        "focused reference search produced no two-existential conjunction derivation"
  | Some derivation ->
      begin
        match witnesses derivation with
        | [left_witness; right_witness] ->
            assert
              (Symbolic_term.compare_flexible
                 left_witness
                 right_witness
               <> 0)
        | _ ->
            assert false
      end

let () =
  match
    Parser.parse_formula
      ~max_modal_index:1
      "forall x. p(x)"
  with
  | Ok
      (Syntax.Forall
         ("x",
          Syntax.Atom
            ("p", [Syntax.Var "x"]))) ->
      ()
  | Ok _ ->
      failwith
        "parser did not treat lowercase bound variable as Syntax.Var"
  | Error message ->
      failwith message

(* Saturation scheduler regression tests: Diff 7. *)

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment -> environment
    | Error message -> failwith message
  in
  let root_position, supply1 =
    Nested_sequent.fresh_position
      Nested_sequent.initial_supply
  in
  let principal, _ =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreOr
         (Syntax.CoreBottom, Syntax.CoreBottom))
  in
  let sequent =
    {
      Nested_sequent.position = root_position;
      formulas = [principal];
      children = [];
    }
  in
  let configuration =
    Saturation_scheduler.create sequent
  in
  assert (Saturation_scheduler.stage configuration = 0);
  match
    Saturation_scheduler.step
      ~environment
      configuration
  with
  | Ok
      (Saturation_scheduler.Applied
         { successors = [successor]; _ }) ->
      assert
        (Saturation_scheduler.stage successor = 1)
  | Ok _ ->
      failwith
        "scheduler did not perform the expected logical step"
  | Error message ->
      failwith message

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment -> environment
    | Error message -> failwith message
  in
  let root_position, supply1 =
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
      Nested_sequent.position = root_position;
      formulas = [bottom];
      children = [];
    }
  in
  let configuration =
    Saturation_scheduler.create sequent
  in
  match
    Saturation_scheduler.step
      ~environment
      configuration
  with
  | Ok (Saturation_scheduler.Bookkeeping successor) ->
      assert
        (Saturation_scheduler.stage successor = 1)
  | Ok _ ->
      failwith
        "scheduler did not perform the expected bookkeeping step"
  | Error message ->
      failwith message

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment -> environment
    | Error message -> failwith message
  in
  let root_position, supply1 =
    Nested_sequent.fresh_position
      Nested_sequent.initial_supply
  in
  let principal, _ =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreAnd
         (Syntax.CoreBottom, Syntax.CoreBottom))
  in
  let sequent =
    {
      Nested_sequent.position = root_position;
      formulas = [principal];
      children = [];
    }
  in
  let code =
    Saturation_scheduler.obligation_code
      (Saturation_scheduler.And
         principal.Nested_sequent.occurrence_id)
  in
  let configuration =
    Saturation_scheduler.create sequent
  in
  let stage_one =
    match
      Saturation_scheduler.step
        ~environment
        configuration
    with
    | Ok (Saturation_scheduler.Bookkeeping successor) ->
        successor
    | Ok _ ->
        failwith
          "conjunction obligation became eligible too early"
    | Error message ->
        failwith message
  in
  match
    Saturation_scheduler.step
      ~environment
      stage_one
  with
  | Ok
      (Saturation_scheduler.Applied
         { successors = [left; right]; _ }) ->
      assert
        (Saturation_scheduler.stage left = 2);
      assert
        (Saturation_scheduler.stage right = 2);
      assert
        (Saturation_scheduler.history left = [code]);
      assert
        (Saturation_scheduler.history right = [code])
  | Ok _ ->
      failwith
        "scheduler did not split the conjunction as expected"
  | Error message ->
      failwith message

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:signature_p1
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment -> environment
    | Error message -> failwith message
  in
  let root_position, supply1 =
    Nested_sequent.fresh_position
      Nested_sequent.initial_supply
  in
  let principal, supply2 =
    Nested_sequent.fresh_formula_occurrence
      supply1
      (Syntax.CoreForall
         ("x", Syntax.CoreBottom))
  in
  let existing_parameter, _ =
    Nested_sequent.fresh_formula_occurrence
      supply2
      (Syntax.PosAtom
         ("p", [Syntax.Param "a0"]))
  in
  let sequent =
    {
      Nested_sequent.position = root_position;
      formulas = [principal; existing_parameter];
      children = [];
    }
  in
  let rec advance_to_logical configuration =
    match
      Saturation_scheduler.step
        ~environment
        configuration
    with
    | Ok (Saturation_scheduler.Bookkeeping successor) ->
        advance_to_logical successor
    | Ok
        (Saturation_scheduler.Applied
           { rule; successors = [successor]; _ }) ->
        rule, successor
    | Ok _ ->
        failwith
          "unexpected scheduler transition while testing canonical parameter freshness"
    | Error message ->
        failwith message
  in
  match
    advance_to_logical
      (Saturation_scheduler.create sequent)
  with
  | Derivation.Forall (_, "a1"), successor ->
      assert
        (Saturation_scheduler.stage successor = 3)
  | Derivation.Forall (_, parameter), _ ->
      failwith
        ("scheduler chose noncanonical fresh proof parameter: "
         ^ parameter)
  | _ ->
      failwith
        "scheduler did not process the universal obligation"

(* Final specification-boundary regression tests. *)

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:signature_p1
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment -> environment
    | Error message -> failwith message
  in
  match
    Symbolic_root.create
      ~environment
      ~program:
        [Syntax.Atom ("p", [Syntax.Var "x"])]
      ~query:Syntax.Bottom
      ~answer_variables:[]
  with
  | Error message ->
      failwith
        ("free program variables were not universally closed: "
         ^ message)
  | Ok root ->
      assert
        (List.exists
           (fun occurrence ->
             match
               occurrence.Symbolic_state.formula
             with
             | Symbolic_formula.Exists
                 ("x",
                  Symbolic_formula.NegAtom
                    ("p", [Symbolic_term.Var "x"])) ->
                 true
             | _ ->
                 false)
           (Symbolic_state.formulas
              (Symbolic_root.state root)))

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:signature_p1
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment -> environment
    | Error message -> failwith message
  in
  match
    Symbolic_root.create
      ~environment
      ~program:[]
      ~query:
        (Syntax.Atom
           ("p", [Syntax.Param "a0"]))
      ~answer_variables:[]
  with
  | Error _ ->
      ()
  | Ok _ ->
      failwith
        "surface query admitted an internal proof parameter"

let () =
  let modality_two =
    match
      Syntax.make_modal_index
        ~max_index:2
        2
    with
    | Ok modality -> modality
    | Error message -> failwith message
  in
  begin
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:
          (Modal_axiom.Set.singleton
             (Modal_axiom.T modality_two))
    with
    | Error _ ->
        ()
    | Ok _ ->
        failwith
          "environment admitted an out-of-range modal axiom"
  end;
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment -> environment
    | Error message -> failwith message
  in
  match
    Symbolic_root.create
      ~environment
      ~program:[]
      ~query:
        (Syntax.Box
           (modality_two, Syntax.Bottom))
      ~answer_variables:[]
  with
  | Error _ ->
      ()
  | Ok _ ->
      failwith
        "surface query admitted an out-of-range modal index"

let () =
  match
    Answer_instance.instantiate
      ~query:
        (Syntax.Atom
           ("p", [Syntax.Var "X"]))
      ~answer_variables:["X"]
      ~answer:
        [("X", Syntax.Var "Y")]
      ~substitution:
        [ ("Y", Syntax.Var "Z");
          ("Z", Syntax.Const "a") ]
  with
  | Ok [("X", Syntax.Var "Z")] ->
      ()
  | Ok _ ->
      failwith
        "answer post-instantiation was not simultaneous"
  | Error message ->
      failwith message

let () =
  let environment =
    match
      Environment.create
        ~max_modal_index:1
        ~signature:Signature.empty
        ~axioms:Modal_axiom.Set.empty
    with
    | Ok environment -> environment
    | Error message -> failwith message
  in
  let truth_root =
    match
      Symbolic_root.create
        ~environment
        ~program:[]
        ~query:(Syntax.Not Syntax.Bottom)
        ~answer_variables:[]
    with
    | Ok root -> root
    | Error message -> failwith message
  in
  let different_root =
    match
      Symbolic_root.create
        ~environment
        ~program:[]
        ~query:Syntax.Bottom
        ~answer_variables:[]
    with
    | Ok root -> root
    | Error message -> failwith message
  in
  let derivation =
    match
      Symbolic_search.derivations_within_depth
        ~environment
        ~depth:0
        (Symbolic_search.of_root truth_root)
    with
    | derivation :: _ -> derivation
    | [] ->
        failwith
          "expected a depth-zero symbolic truth derivation"
  in
  let solved =
    match
      Symbolic_search.solve_derivation derivation
    with
    | Some solved -> solved
    | None ->
        failwith
          "failed to solve symbolic truth derivation"
  in
  match
    Trusted_answer.certify
      ~environment
      ~root:different_root
      solved
  with
  | Error _ ->
      ()
  | Ok _ ->
      failwith
        "trusted certification accepted a derivation for a different root"
