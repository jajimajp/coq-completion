(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom right_inverse : forall X : G, (multiply X (inverse X)) = identity.
Axiom right_identity : forall X : G, (multiply X identity) = X.
Axiom associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : G, (multiply identity X) = X.

Complete right_inverse right_identity associativity left_inverse left_identity :  : hint
  for ((inverse identity) = identity).

(* Goal *)
Theorem check : (inverse identity) = identity.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

