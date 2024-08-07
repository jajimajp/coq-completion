(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom c08 : forall A B C : G, (mult (mult A B) (ld B (mult C B))) = (mult (mult A C) B).
Axiom c07 : forall A B C : G, (mult (rd (mult A B) A) (mult A C)) = (mult A (mult B C)).
Axiom c06 : forall A B : G, (mult (rd A B) B) = A.
Axiom c05 : forall A B : G, (rd (mult A B) B) = A.
Axiom c04 : forall A B : G, (ld A (mult A B)) = B.
Axiom c03 : forall A B : G, (mult A (ld A B)) = B.
Axiom c02 : forall A : G, (mult A unit) = A.
Axiom c01 : forall A : G, (mult unit A) = A.

Complete c08 c07 c06 c05 c04 c03 c02 c01 : ld mult rd unit : hint
  for ((mult a (mult b (ld (mult c d) (mult d c)))) = (mult (mult a b) (ld (mult c d) (mult d c)))).

(* Goal *)
Theorem check : (mult a (mult b (ld (mult c d) (mult d c)))) = (mult (mult a b) (ld (mult c d) (mult d c))).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

