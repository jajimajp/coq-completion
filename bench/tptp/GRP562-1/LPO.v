(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom multiply : forall A B : G, (multiply A B) = (divide A (inverse B)).
Axiom single_axiom : forall A B C : G, (divide (divide (divide A (inverse B)) C) (divide A C)) = B.

Complete multiply single_axiom :  : hint
  for ((multiply (multiply (inverse b2) b2) a2) = a2).

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

