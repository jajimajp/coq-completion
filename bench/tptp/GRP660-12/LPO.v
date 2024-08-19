(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom f05 : forall A B C : G, (mult (mult (mult A B) C) A) = (mult A (mult B (mult C A))).
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.

Complete f05 f04 f03 f02 f01 :  : hint
  for ((mult (rd x1 x1) x0) = x0).

(* Goal *)
Theorem check : (mult (rd x1 x1) x0) = x0.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

