(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Axiom f06 : forall A B C : G, (mult (mult A B) C) = (mult (mult A C) (mult B (ld C C))).
Axiom f05 : forall A B C : G, (mult A (mult B C)) = (mult (mult (rd A A) B) (mult A C)).
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult (mult a (mult a a)) (mult b c)) = (mult (mult a b) (mult (mult a a) c)).
Proof.
  hammer.
Qed.

Check check.

