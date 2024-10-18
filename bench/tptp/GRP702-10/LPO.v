(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter op_c : G.
Parameter op_d : G.
Parameter op_e : G.
Parameter op_f : G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Parameter x0 : G.
Parameter x1 : G.
Hint Resolve op_c.
Axiom ax_f13 : forall A B : G, op_f = (mult A (mult B (ld (mult A B) op_c))).
Axiom ax_f12 : forall A B : G, op_e = (mult (mult (rd op_c (mult A B)) B) A).
Axiom ax_f11 : forall A : G, op_d = (ld A (mult op_c A)).
Axiom ax_f10 : forall A B : G, (mult A (mult op_c B)) = (mult (mult A op_c) B).
Axiom ax_f09 : forall A B : G, (mult A (mult B op_c)) = (mult (mult A B) op_c).
Axiom ax_f08 : forall A B : G, (mult op_c (mult A B)) = (mult (mult op_c A) B).
Axiom ax_f07 : forall A B C : G, (mult A (mult B (mult B C))) = (mult (mult (mult A B) B) C).
Axiom ax_f06 : forall A : G, (mult unit A) = A.
Axiom ax_f05 : forall A : G, (mult A unit) = A.
Axiom ax_f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : G, (mult A (ld A B)) = B.

Complete ax_f13 ax_f12 ax_f11 ax_f10 ax_f09 ax_f08 ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 : ld mult op_c op_d op_e op_f rd unit x0 x1 : hint
  for ((mult op_d (mult x0 x1)) = (mult (mult op_d x0) x1)).

(* Goal *)
Theorem check : (mult op_d (mult x0 x1)) = (mult (mult op_d x0) x1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

