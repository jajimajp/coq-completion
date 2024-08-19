(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom f05 : forall A B C : G, (mult (mult A (mult B B)) C) = (mult (mult A B) (mult B C)).
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : forall X0 : G, (tuple (mult X0 (x1 X0)) (mult (x1_2 X0) X0)) = (tuple (x1 X0) (x1_2 X0)).
Proof.
  hammer.
Qed.

Check check.

