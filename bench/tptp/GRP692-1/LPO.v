(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom c13 : (mult op_e op_e) = op_f.
Axiom c12 : (mult op_d op_d) = op_e.
Axiom c11 : (mult op_c (mult op_c op_c)) = op_d.
Axiom c10 : forall A : G, (mult A (i A)) = unit.
Axiom c09 : forall A : G, (mult (i A) A) = unit.
Axiom c08 : forall A B C : G, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom c07 : forall A B C : G, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom c06 : forall A : G, (mult unit A) = A.
Axiom c05 : forall A : G, (mult A unit) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.

Complete c13 c12 c11 c10 c09 c08 c07 c06 c05 c04 c03 c02 c01 :  : hint
  for ((mult op_e (mult a (mult b op_e))) = (mult (mult (mult op_e a) b) op_e)).

(* Goal *)
Theorem check : (mult op_e (mult a (mult b op_e))) = (mult (mult (mult op_e a) b) op_e).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

