(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Axiom c05 : forall A B : G, (mult (rd A B) B) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (ld A (mult A B)) = B.
Axiom c02 : forall A B : G, (mult A (ld A B)) = B.
Axiom c01 : forall A B C : G, (mult A (mult B C)) = (mult (mult A B) (mult A C)).

Complete c05 c04 c03 c02 c01 : ld mult rd : hint
  for ((mult (mult a b) (mult c d)) = (mult (mult a c) (mult b d))).

(* Goal *)
Theorem check : (mult (mult a b) (mult c d)) = (mult (mult a c) (mult b d)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.
