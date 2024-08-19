(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter i : G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom c10 : forall A B : G, (mult A B) = (mult B A).
Axiom c09 : forall A B C : G, (mult (mult A B) (mult C (mult A B))) = (mult (mult (mult A (mult B C)) A) B).
Axiom c08 : forall A B : G, (mult (mult A B) (i B)) = A.
Axiom c07 : forall A B : G, (mult (i A) (mult A B)) = B.
Axiom c06 : forall A : G, (mult unit A) = A.
Axiom c05 : forall A : G, (mult A unit) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.

Complete c10 c09 c08 c07 c06 c05 c04 c03 c02 c01 : i ld mult rd unit : hint
  for ((mult a (mult (mult b (mult b b)) (mult (mult b (mult b b)) c))) = (mult (mult (mult a (mult b (mult b b))) (mult b (mult b b))) c)).

(* Goal *)
Theorem check : (mult a (mult (mult b (mult b b)) (mult (mult b (mult b b)) c))) = (mult (mult (mult a (mult b (mult b b))) (mult b (mult b b))) c).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

