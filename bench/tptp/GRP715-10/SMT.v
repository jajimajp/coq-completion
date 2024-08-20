(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable minus : Z -> Z.
Variable mult : Z -> Z -> Z.
Variable op_0 : Z.
Variable op_a : Z.
Variable op_b : Z.
Variable plus : Z -> Z -> Z.
Variable unit : Z.
Variable x0 : Z.
Axiom ax_f11 : (mult op_b op_a) =? unit.
Axiom ax_f10 : (mult op_a op_b) =? unit.
Axiom ax_f09 : forall A : Z, (mult unit A) =? A.
Axiom ax_f08 : forall A : Z, (mult A unit) =? A.
Axiom ax_f07 : forall A B : Z, (mult A (mult B B)) =? (mult (mult A B) B).
Axiom ax_f06 : forall A B C : Z, (mult (mult (mult A B) C) B) =? (mult A (mult (mult B C) B)).
Axiom ax_f05 : forall A B C : Z, (mult A (plus B C)) =? (plus (mult A B) (mult A C)).
Axiom ax_f04 : forall A : Z, (plus A (minus A)) =? op_0.
Axiom ax_f03 : forall A : Z, (plus A op_0) =? A.
Axiom ax_f02 : forall A B : Z, (plus A B) =? (plus B A).
Axiom ax_f01 : forall A B C : Z, (plus (plus A B) C) =? (plus A (plus B C)).

Add_lemmas ax_f11 ax_f10 ax_f09 ax_f08 ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01.

(* Goal *)
Theorem check : (mult (mult x0 op_a) op_b) =? x0.
Proof.
  smt.
Qed.

Check check.

