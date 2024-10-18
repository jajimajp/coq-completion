(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter identity : G.
Parameter left_division : G -> G -> G.
Parameter left_inverse : G -> G.
Parameter multiply : G -> G -> G.
Parameter right_division : G -> G -> G.
Parameter right_inverse : G -> G.
Hint Resolve a.
Axiom ax_moufang2 : forall X Y Z : G, (multiply (multiply (multiply X Y) Z) Y) = (multiply X (multiply Y (multiply Z Y))).
Axiom ax_left_inverse : forall X : G, (multiply (left_inverse X) X) = identity.
Axiom ax_right_inverse : forall X : G, (multiply X (right_inverse X)) = identity.
Axiom ax_right_division_multiply : forall X Y : G, (right_division (multiply X Y) Y) = X.
Axiom ax_multiply_right_division : forall X Y : G, (multiply (right_division X Y) Y) = X.
Axiom ax_left_division_multiply : forall X Y : G, (left_division X (multiply X Y)) = Y.
Axiom ax_multiply_left_division : forall X Y : G, (multiply X (left_division X Y)) = Y.
Axiom ax_right_identity : forall X : G, (multiply X identity) = X.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.

Complete ax_moufang2 ax_left_inverse ax_right_inverse ax_right_division_multiply ax_multiply_right_division ax_left_division_multiply ax_multiply_left_division ax_right_identity ax_left_identity : a b c identity left_division left_inverse multiply right_division right_inverse : hint
  for ((multiply (multiply (multiply a b) a) c) = (multiply a (multiply b (multiply a c)))).

(* Goal *)
Theorem check : (multiply (multiply (multiply a b) a) c) = (multiply a (multiply b (multiply a c))).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

