(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : G, (multiply identity X) = X.

Complete associativity left_inverse left_identity : identity inverse multiply : hint
  for ((multiply sk_c1 sk_c9) = sk_c8).

(* Goal *)
Theorem check : (multiply sk_c1 sk_c9) = sk_c8.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

