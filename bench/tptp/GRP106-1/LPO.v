(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom multiply : forall X Y : G, (multiply X Y) = (inverse (double_divide Y X)).
Axiom single_axiom : forall X Y Z : G, (inverse (double_divide (double_divide X Y) (inverse (double_divide X (inverse (double_divide Z Y)))))) = Z.

Complete multiply single_axiom :  : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

