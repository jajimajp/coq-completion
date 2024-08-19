(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom identity : forall X : G, identity = (divide X X).
Axiom inverse : forall X Z : G, (inverse X) = (divide (divide Z Z) X).
Axiom multiply : forall X Y Z : G, (multiply X Y) = (divide X (divide (divide Z Z) Y)).
Axiom single_axiom : forall X Y Z : G, (divide (divide X (divide (divide X Y) Z)) Y) = Z.

Complete identity inverse multiply single_axiom :  : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

