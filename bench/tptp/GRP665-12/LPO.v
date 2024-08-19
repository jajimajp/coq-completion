(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom f09 : forall A : G, (mult op_c A) = (mult A op_c).
Axiom f08 : forall A B C : G, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom f07 : forall A B C : G, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom f06 : forall A : G, (mult unit A) = A.
Axiom f05 : forall A : G, (mult A unit) = A.
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.

Complete f09 f08 f07 f06 f05 f04 f03 f02 f01 :  : hint
  for ((mult (mult x0 x1) op_c) = (mult x0 (mult x1 op_c))).

(* Goal *)
Theorem check : (mult (mult x0 x1) op_c) = (mult x0 (mult x1 op_c)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

