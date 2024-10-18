(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a.
Axiom ax_right_inverse : forall X : G, (multiply X (inverse X)) = identity.
Axiom ax_right_identity : forall X : G, (multiply X identity) = X.
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.

Complete ax_right_inverse ax_right_identity ax_associativity ax_left_inverse ax_left_identity : a identity inverse multiply : hint
  for ((inverse (inverse a)) = a).

(* Goal *)
Theorem check : (inverse (inverse a)) = a.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

