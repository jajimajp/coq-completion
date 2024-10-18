(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter a4 : G.
Parameter b3 : G.
Parameter b4 : G.
Parameter c3 : G.
Parameter double_divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a1.
Axiom ax_identity : forall X : G, identity = (double_divide X (inverse X)).
Axiom ax_inverse : forall X : G, (inverse X) = (double_divide X identity).
Axiom ax_multiply : forall X Y : G, (multiply X Y) = (double_divide (double_divide Y X) identity).
Axiom ax_single_axiom : forall X Y Z : G, (double_divide (double_divide X (double_divide (double_divide Y (double_divide Z X)) (double_divide Z identity))) (double_divide identity identity)) = Y.

Complete ax_identity ax_inverse ax_multiply ax_single_axiom : a1 a2 a3 a4 b3 b4 c3 double_divide identity inverse multiply : hint
  for ((multiply (inverse a1) a1) = identity).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

