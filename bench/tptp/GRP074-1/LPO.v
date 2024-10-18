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
Parameter divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a1.
Axiom ax_multiply : forall X Y : G, (multiply X Y) = (divide X (inverse Y)).
Axiom ax_single_axiom : forall U X Y Z : G, (divide (inverse (divide (divide (divide X X) Y) (divide Z (divide Y U)))) U) = Z.

Complete ax_multiply ax_single_axiom : a1 a2 a3 b1 b2 b3 c3 divide inverse multiply : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

