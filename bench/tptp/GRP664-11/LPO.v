(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Parameter x0 : G.
Parameter x1 : G.
Parameter x2 : G.
Parameter x3 : G.
Hint Resolve unit.
Axiom ax_goal1 : (mult x0 x1) = unit.
Axiom ax_f08 : forall A B C : G, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom ax_f07 : forall A B C : G, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom ax_f06 : forall A : G, (mult unit A) = A.
Axiom ax_f05 : forall A : G, (mult A unit) = A.
Axiom ax_f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : G, (mult A (ld A B)) = B.

Complete ax_goal1 ax_f08 ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 : ld mult rd unit x0 x1 x2 x3 : hint
  for ((mult (mult x2 (mult x1 x0)) x3) = (mult x2 (mult (mult x1 x0) x3))).

(* Goal *)
Theorem check : (mult (mult x2 (mult x1 x0)) x3) = (mult x2 (mult (mult x1 x0) x3)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

