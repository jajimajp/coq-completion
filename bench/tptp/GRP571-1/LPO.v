(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom identity : forall A : G, identity = (double_divide A (inverse A)).
Axiom inverse : forall A : G, (inverse A) = (double_divide A identity).
Axiom multiply : forall A B : G, (multiply A B) = (double_divide (double_divide B A) identity).
Axiom single_axiom : forall A B C : G, (double_divide (double_divide A (double_divide (double_divide B (double_divide A C)) (double_divide C identity))) (double_divide identity identity)) = B.

Complete identity inverse multiply single_axiom :  : hint
  for ((multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3))).

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

