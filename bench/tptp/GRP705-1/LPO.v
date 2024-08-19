(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom c09 : (mult op_b (mult op_b (mult op_b (mult op_b (mult op_b (mult op_b (mult op_b (mult op_b op_b)))))))) = unit.
Axiom c08 : (mult op_a (mult op_a (mult op_a op_a))) = unit.
Axiom c07 : forall A B C : G, (mult A (mult B (mult B C))) = (mult (mult (mult A B) B) C).
Axiom c06 : forall A : G, (mult unit A) = A.
Axiom c05 : forall A : G, (mult A unit) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.

Complete c09 c08 c07 c06 c05 c04 c03 c02 c01 :  : hint
  for ((mult op_a (mult op_b a)) = (mult (mult op_a op_b) a)).

(* Goal *)
Theorem check : (mult op_a (mult op_b a)) = (mult (mult op_a op_b) a).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

