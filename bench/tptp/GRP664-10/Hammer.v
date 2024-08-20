(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Parameter x0 : G.
Parameter x1 : G.
Axiom goal1 : (mult x0 x1) = unit.
Axiom f08 : forall A B C : G, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom f07 : forall A B C : G, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom f06 : forall A : G, (mult unit A) = A.
Axiom f05 : forall A : G, (mult A unit) = A.
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult (mult x1 x0) (mult x2 x3)) = (mult (mult (mult x1 x0) x2) x3).
Proof.
  hammer.
Qed.

Check check.

