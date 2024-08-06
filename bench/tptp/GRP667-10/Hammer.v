(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter f : G -> G.
Parameter ifeq : G -> G -> G -> G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom f12 : forall X6 X7 X8 : G, (ifeq (mult (mult X6 X7) (mult X8 X6)) (mult X6 (mult (mult X7 X8) X6)) (mult X6 (mult X7 (mult X6 X8))) (mult (mult (mult X6 X7) X6) X8)) = (mult (mult (mult X6 X7) X6) X8).
Axiom f11 : forall X3 X4 X5 : G, (ifeq (mult (mult X3 X4) (mult X5 X3)) (mult (mult X3 (mult X4 X5)) X3) (mult X3 (mult X4 (mult X3 X5))) (mult (mult (mult X3 X4) X3) X5)) = (mult (mult (mult X3 X4) X3) X5).
Axiom f10 : forall X0 X1 X2 : G, (ifeq (mult X0 (mult X1 (mult X2 X1))) (mult (mult (mult X0 X1) X2) X1) (mult X1 (mult X0 (mult X1 X2))) (mult (mult (mult X1 X0) X1) X2)) = (mult (mult (mult X1 X0) X1) X2).
Axiom f09 : forall A : G, (mult (f A) (f A)) = A.
Axiom f08 : forall A B : G, (mult (mult A B) A) = (mult A (mult B A)).
Axiom f07 : forall A B C : G, (mult (mult A B) (mult (mult C B) C)) = (mult (mult A (mult (mult B C) B)) C).
Axiom f06 : forall A : G, (mult unit A) = A.
Axiom f05 : forall A : G, (mult A unit) = A.
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.
Axiom ifeq_axiom : forall A B C : G, (ifeq A A B C) = B.


(* Goal *)
Theorem check : (mult a (mult b (mult a c))) = (mult (mult (mult a b) a) c).
Proof.
  hammer.
Qed.

Check check.
