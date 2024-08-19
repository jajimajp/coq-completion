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
Axiom c11 : forall A B : G, (mult (mult A B) (i B)) = A.
Axiom c10 : forall A B : G, (mult (i A) (mult A B)) = B.
Axiom c09 : forall A B C : G, (ld A (mult (mult B C) A)) = (mult (ld A (mult B A)) (ld A (mult C A))).
Axiom c08 : forall A B C D : G, (rd (mult (mult (mult A B) C) D) (mult C D)) = (mult (rd (mult (mult A C) D) (mult C D)) (rd (mult (mult B C) D) (mult C D))).
Axiom c07 : forall A B C D : G, (ld (mult A B) (mult A (mult B (mult C D)))) = (mult (ld (mult A B) (mult A (mult B C))) (ld (mult A B) (mult A (mult B D)))).
Axiom c06 : forall A : G, (mult unit A) = A.
Axiom c05 : forall A : G, (mult A unit) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.

Complete c11 c10 c09 c08 c07 c06 c05 c04 c03 c02 c01 : i ld mult rd unit : hint
  for ((mult (mult a b) (mult c a)) = (mult (mult a (mult b c)) a)).

(* Goal *)
Theorem check : (mult (mult a b) (mult c a)) = (mult (mult a (mult b c)) a).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

