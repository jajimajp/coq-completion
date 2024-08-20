(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter b1 : G.
Parameter b2 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_multiply : forall X Y : G, (multiply X Y) = (inverse (double_divide Y X)).
Axiom ax_single_axiom : forall U X Y Z : G, (inverse (double_divide (double_divide X (double_divide (double_divide Y Z) (inverse (double_divide Y (double_divide (inverse U) (inverse Z)))))) X)) = U.

Complete ax_multiply ax_single_axiom : a1 a2 a3 b1 b2 b3 c3 double_divide inverse multiply : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

