(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter identity : G.
Parameter multiply : G -> G -> G.
Axiom left_identity : forall X : G, (multiply identity X) = X.
Axiom associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).

Complete left_identity associativity : identity multiply : hint
  for (forall X : G, (multiply X X) = identity).

(* Goal *)
Theorem check : forall X : G, (multiply X X) = identity.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.
