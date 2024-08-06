(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter minus : G -> G.
Parameter mult : G -> G -> G.
Parameter op_0 : G.
Parameter op_a : G.
Parameter op_b : G.
Parameter plus : G -> G -> G.
Parameter unit : G.
Axiom c11 : (mult op_b op_a) = unit.
Axiom c10 : (mult op_a op_b) = unit.
Axiom c09 : forall A : G, (mult unit A) = A.
Axiom c08 : forall A : G, (mult A unit) = A.
Axiom c07 : forall A B : G, (mult A (mult B B)) = (mult (mult A B) B).
Axiom c06 : forall A B C : G, (mult (mult (mult A B) C) B) = (mult A (mult (mult B C) B)).
Axiom c05 : forall A B C : G, (mult A (plus B C)) = (plus (mult A B) (mult A C)).
Axiom c04 : forall A : G, (plus A (minus A)) = op_0.
Axiom c03 : forall A : G, (plus A op_0) = A.
Axiom c02 : forall A B : G, (plus A B) = (plus B A).
Axiom c01 : forall A B C : G, (plus (plus A B) C) = (plus A (plus B C)).

Complete c11 c10 c09 c08 c07 c06 c05 c04 c03 c02 c01 : minus mult op_0 op_a op_b plus unit : hint
  for ((mult op_a (mult (mult op_b (mult a op_b)) op_a)) = a).

(* Goal *)
Theorem check : (mult op_a (mult (mult op_b (mult a op_b)) op_a)) = a.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.
