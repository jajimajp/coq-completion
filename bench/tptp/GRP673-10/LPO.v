(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter asoc : G -> G -> G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter op_t : G.
Parameter op_x : G.
Parameter op_y : G.
Parameter op_z : G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom f09 : (mult op_t (asoc op_x op_y op_z)) = (mult (asoc op_x op_y op_z) op_t).
Axiom f08 : forall A B C : G, (asoc A B C) = (ld (mult A (mult B C)) (mult (mult A B) C)).
Axiom f07 : forall A B C : G, (mult A (mult B (mult C A))) = (mult (mult (mult A B) C) A).
Axiom f06 : forall A : G, (mult unit A) = A.
Axiom f05 : forall A : G, (mult A unit) = A.
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.

Complete f09 f08 f07 f06 f05 f04 f03 f02 f01 : asoc ld mult op_t op_x op_y op_z rd unit : hint
  for ((mult op_z (asoc op_x op_y op_t)) = (mult (asoc op_x op_y op_t) op_z)).

(* Goal *)
Theorem check : (mult op_z (asoc op_x op_y op_t)) = (mult (asoc op_x op_y op_t) op_z).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

