(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom identity : forall A : G, identity = (double_divide A (inverse A)).
Axiom inverse : forall A : G, (inverse A) = (double_divide A identity).
Axiom multiply : forall A B : G, (multiply A B) = (double_divide (double_divide B A) identity).
Axiom single_axiom : forall A B C : G, (double_divide (double_divide A (double_divide (double_divide B (double_divide C A)) (double_divide C identity))) (double_divide identity identity)) = B.

Complete identity inverse multiply single_axiom :  : hint
  for ((multiply a b) = (multiply b a)).

(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

