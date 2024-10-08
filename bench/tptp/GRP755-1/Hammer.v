(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter i : G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom ax_f09 : forall A : G, (i A) = (ld A unit).
Axiom ax_f08 : forall A B C : G, (mult A (mult B C)) = (mult (mult A B) C).
Axiom ax_f07 : forall A B C : G, (mult A (mult B C)) = (mult (mult A B) C).
Axiom ax_f06 : forall A : G, (mult unit A) = A.
Axiom ax_f05 : forall A : G, (mult A unit) = A.
Axiom ax_f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (i (mult a b)) = (mult (i b) (i a)).
Proof.
  hammer.
Qed.

Check check.

