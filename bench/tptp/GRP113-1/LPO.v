(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_c_not_identity : c = identity.
Axiom ax_b_not_identity : b = identity.
Axiom ax_b_not_c : b = c.
Axiom ax_a_not_identity : a = identity.
Axiom ax_a_not_c : a = c.
Axiom ax_a_not_b : a = b.
Axiom ax_all_of_group1 : forall X : G, X = a.
Axiom ax_right_inverse : forall X : G, (multiply X (inverse X)) = identity.
Axiom ax_right_identity : forall X : G, (multiply X identity) = X.
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.

Complete ax_c_not_identity ax_b_not_identity ax_b_not_c ax_a_not_identity ax_a_not_c ax_a_not_b ax_all_of_group1 ax_right_inverse ax_right_identity ax_associativity ax_left_inverse ax_left_identity : a b c identity inverse multiply : hint
  for ((multiply a a) = identity).

(* Goal *)
Theorem check : (multiply a a) = identity.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

