(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom inverse : forall A B : G, (inverse A) = (divide (divide B B) A).
Axiom multiply : forall A B C : G, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom single_axiom : forall A B C : G, (divide A (divide (divide (divide (divide B B) B) C) (divide (divide (divide B B) A) C))) = B.

Complete inverse multiply single_axiom :  : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

