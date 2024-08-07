(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter op_c : G.
Parameter op_d : G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom c09 : forall A : G, (mult op_d A) = (mult A op_d).
Axiom c08 : forall A : G, (mult op_c A) = (mult A op_c).
Axiom c07 : forall A B C : G, (mult A (mult B (mult A C))) = (mult (mult A (mult B A)) C).
Axiom c06 : forall A : G, (mult unit A) = A.
Axiom c05 : forall A : G, (mult A unit) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult (mult (mult op_c op_c) op_d) a) = (mult a (mult (mult op_c op_c) op_d)).
Proof.
  hammer.
Qed.

Check check.

