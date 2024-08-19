(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom identity : forall A : G, identity = (divide A A).
Axiom inverse : forall A : G, (inverse A) = (divide identity A).
Axiom multiply : forall A B : G, (multiply A B) = (divide A (divide identity B)).
Axiom single_axiom : forall A B C : G, (divide (divide identity A) (divide (divide (divide B A) C) B)) = C.

Complete identity inverse multiply single_axiom :  : hint
  for ((multiply (multiply (inverse b2) b2) a2) = a2).

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

