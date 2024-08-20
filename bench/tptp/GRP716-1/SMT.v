(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable minus : Z -> Z.
Variable mult : Z -> Z -> Z.
Variable op_0 : Z.
Variable op_a : Z.
Variable op_b : Z.
Variable plus : Z -> Z -> Z.
Variable unit : Z.
Axiom ax_c11 : (mult op_b op_a) =? unit.
Axiom ax_c10 : (mult op_a op_b) =? unit.
Axiom ax_c09 : forall A : Z, (mult unit A) =? A.
Axiom ax_c08 : forall A : Z, (mult A unit) =? A.
Axiom ax_c07 : forall A B : Z, (mult A (mult B B)) =? (mult (mult A B) B).
Axiom ax_c06 : forall A B C : Z, (mult (mult (mult A B) C) B) =? (mult A (mult (mult B C) B)).
Axiom ax_c05 : forall A B C : Z, (mult A (plus B C)) =? (plus (mult A B) (mult A C)).
Axiom ax_c04 : forall A : Z, (plus A (minus A)) =? op_0.
Axiom ax_c03 : forall A : Z, (plus A op_0) =? A.
Axiom ax_c02 : forall A B : Z, (plus A B) =? (plus B A).
Axiom ax_c01 : forall A B C : Z, (plus (plus A B) C) =? (plus A (plus B C)).

Add_lemmas ax_c11 ax_c10 ax_c09 ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01.

(* Goal *)
Theorem check : (mult op_a (mult (mult op_b (mult a op_b)) op_a)) =? a.
Proof.
  smt.
Qed.

Check check.

