(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom f06 : forall A B C : G, (mult (mult A A) (mult B C)) = (mult (mult A B) (mult A C)).
Axiom f05 : forall A B C : G, (mult (mult A (mult A A)) (mult B C)) = (mult (mult A B) (mult (mult A A) C)).
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.

Complete f06 f05 f04 f03 f02 f01 :  : hint
  for ((mult (mult a b) (mult c c)) = (mult (mult a c) (mult b c))).

(* Goal *)
Theorem check : (mult (mult a b) (mult c c)) = (mult (mult a c) (mult b c)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

