(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom identity : forall A : G, identity = (divide A A).
Axiom inverse : forall A : G, (inverse A) = (divide identity A).
Axiom multiply : forall A B : G, (multiply A B) = (divide A (divide identity B)).
Axiom single_axiom : forall A B C : G, (divide (divide identity (divide A (divide B (divide (divide (divide A A) A) C)))) C) = B.

Complete identity inverse multiply single_axiom : divide identity inverse multiply : hint
  for ((multiply identity a2) = a2).

(* Goal *)
Theorem check : (multiply identity a2) = a2.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

