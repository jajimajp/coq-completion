(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom c09 : forall A B : G, (mult A B) = (mult B A).
Axiom c08 : forall A : G, (s (mult A A)) = A.
Axiom c07 : forall A : G, (mult (s A) (s A)) = A.
Axiom c06 : forall A B C : G, (ld A (mult (mult B C) A)) = (mult (ld A (mult B A)) (ld A (mult C A))).
Axiom c05 : forall A B C D : G, (ld (mult A B) (mult A (mult B (mult C D)))) = (mult (ld (mult A B) (mult A (mult B C))) (ld (mult A B) (mult A (mult B D)))).
Axiom c04 : forall A B : G, (ld A (mult A B)) = B.
Axiom c03 : forall A B : G, (mult A (ld A B)) = B.
Axiom c02 : forall A : G, (mult unit A) = A.
Axiom c01 : forall A : G, (mult A unit) = A.


(* Goal *)
Theorem check : (mult (mult a b) c) = (mult a (mult b c)).
Proof.
  hammer.
Qed.

Check check.

