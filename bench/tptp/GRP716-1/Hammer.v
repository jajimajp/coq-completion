(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter minus : G -> G.
Parameter mult : G -> G -> G.
Parameter op_0 : G.
Parameter op_a : G.
Parameter op_b : G.
Parameter plus : G -> G -> G.
Parameter unit : G.
Axiom ax_c11 : (mult op_b op_a) = unit.
Axiom ax_c10 : (mult op_a op_b) = unit.
Axiom ax_c09 : forall A : G, (mult unit A) = A.
Axiom ax_c08 : forall A : G, (mult A unit) = A.
Axiom ax_c07 : forall A B : G, (mult A (mult B B)) = (mult (mult A B) B).
Axiom ax_c06 : forall A B C : G, (mult (mult (mult A B) C) B) = (mult A (mult (mult B C) B)).
Axiom ax_c05 : forall A B C : G, (mult A (plus B C)) = (plus (mult A B) (mult A C)).
Axiom ax_c04 : forall A : G, (plus A (minus A)) = op_0.
Axiom ax_c03 : forall A : G, (plus A op_0) = A.
Axiom ax_c02 : forall A B : G, (plus A B) = (plus B A).
Axiom ax_c01 : forall A B C : G, (plus (plus A B) C) = (plus A (plus B C)).


(* Goal *)
Theorem check : (mult op_a (mult (mult op_b (mult a op_b)) op_a)) = a.
Proof.
  hammer.
Qed.

Check check.

