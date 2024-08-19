(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom f05 : forall A : G, (mult (i A) A) = unit.
Axiom f04 : forall A : G, (mult A (i A)) = unit.
Axiom f03 : forall A B C : G, (mult A (mult B (mult B C))) = (mult (mult (mult A B) B) C).
Axiom f02 : forall A : G, (mult unit A) = A.
Axiom f01 : forall A : G, (mult A unit) = A.


(* Goal *)
Theorem check : forall X5 : G, (mult X5 x4) = x3.
Proof.
  hammer.
Qed.

Check check.

