(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter mult : G -> G -> G.
Parameter unit : G.
Parameter x0 : G.
Parameter x1 : G.
Axiom f08 : forall A B C : G, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom f07 : forall A B C : G, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom f06 : forall A : G, (mult unit A) = A.
Axiom f05 : forall A : G, (mult A unit) = A.
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.

Complete f08 f07 f06 f05 f04 f03 f02 f01 : mult unit x0 x1 : hint
  for ((mult x0 x1) = unit).

(* Goal *)
Theorem check : (mult x0 x1) = unit.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

