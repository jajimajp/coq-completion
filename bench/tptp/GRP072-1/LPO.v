(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom multiply : forall X Y : G, (multiply X Y) = (divide X (inverse Y)).
Axiom single_axiom : forall U X Y Z : G, (divide (divide (inverse (divide X Y)) (divide (divide Z U) X)) (divide U Z)) = Y.

Complete multiply single_axiom :  : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

