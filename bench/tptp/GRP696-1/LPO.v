(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom c11 : forall A : G, (mult A (i A)) = unit.
Axiom c10 : forall A : G, (mult (i A) A) = unit.
Axiom c09 : forall A B C : G, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom c08 : forall A B C : G, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom c07 : forall A B : G, (mult A (i (mult B A))) = (i B).
Axiom c06 : forall A : G, (mult unit A) = A.
Axiom c05 : forall A : G, (mult A unit) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.

Complete c11 c10 c09 c08 c07 c06 c05 c04 c03 c02 c01 :  : hint
  for ((mult (mult (mult a b) a) (mult a c)) = (mult a (mult (mult (mult b a) a) c))).

(* Goal *)
Theorem check : (mult (mult (mult a b) a) (mult a c)) = (mult a (mult (mult (mult b a) a) c)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

