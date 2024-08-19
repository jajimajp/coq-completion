(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom c08 : forall A B C : G, (mult (mult A B) (mult B (mult C B))) = (mult (mult A (mult B (mult B C))) B).
Axiom c07 : forall A B C : G, (mult (mult (mult A B) A) (mult A C)) = (mult A (mult (mult (mult B A) A) C)).
Axiom c06 : forall A : G, (mult unit A) = A.
Axiom c05 : forall A : G, (mult A unit) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult a (mult b c)) = (mult (rd (mult a b) a) (mult a c)).
Proof.
  hammer.
Qed.

Check check.

