(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom f13 : forall A B : G, op_f = (mult A (mult B (ld (mult A B) op_c))).
Axiom f12 : forall A B : G, op_e = (mult (mult (rd op_c (mult A B)) B) A).
Axiom f11 : forall A : G, op_d = (ld A (mult op_c A)).
Axiom f10 : forall A B : G, (mult A (mult op_c B)) = (mult (mult A op_c) B).
Axiom f09 : forall A B : G, (mult A (mult B op_c)) = (mult (mult A B) op_c).
Axiom f08 : forall A B : G, (mult op_c (mult A B)) = (mult (mult op_c A) B).
Axiom f07 : forall A B C : G, (mult A (mult B (mult B C))) = (mult (mult (mult A B) B) C).
Axiom f06 : forall A : G, (mult unit A) = A.
Axiom f05 : forall A : G, (mult A unit) = A.
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.

Complete f13 f12 f11 f10 f09 f08 f07 f06 f05 f04 f03 f02 f01 :  : hint
  for ((mult x4 (mult op_f x5)) = (mult (mult x4 op_f) x5)).

(* Goal *)
Theorem check : (mult x4 (mult op_f x5)) = (mult (mult x4 op_f) x5).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

