(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom c11 : (mult op_d (mult op_d (mult op_d (mult op_d (mult op_d (mult op_d (mult op_d (mult op_d op_d)))))))) = unit.
Axiom c10 : (mult op_c (mult op_c (mult op_c op_c))) = unit.
Axiom c09 : forall A B : G, (i (mult A B)) = (mult (i A) (i B)).
Axiom c08 : forall A B : G, (mult (i A) (mult A B)) = B.
Axiom c07 : forall A B C : G, (mult A (mult B (mult A C))) = (mult (mult A (mult B A)) C).
Axiom c06 : forall A : G, (mult unit A) = A.
Axiom c05 : forall A : G, (mult A unit) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult op_c op_d) = (mult op_d op_c).
Proof.
  hammer.
Qed.

Check check.

