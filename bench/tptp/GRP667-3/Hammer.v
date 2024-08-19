(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter f : G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom c09 : forall A : G, (mult (f A) (f A)) = A.
Axiom c08 : forall A B : G, (mult (mult A B) A) = (mult A (mult B A)).
Axiom c07 : forall A B C : G, (mult (mult A B) (mult (mult C B) C)) = (mult (mult A (mult (mult B C) B)) C).
Axiom c06 : forall A : G, (mult unit A) = A.
Axiom c05 : forall A : G, (mult A unit) = A.
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult a (mult b (mult c b))) = (mult (mult (mult a b) c) b).
Proof.
  hammer.
Qed.

Check check.

