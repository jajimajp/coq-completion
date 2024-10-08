(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Variable x0 : Z.
Variable x1 : Z.
Variable x2 : Z.
Variable x3 : Z.
Axiom ax_goal1 : (mult x0 x1) =? unit.
Axiom ax_f08 : forall A B C : Z, (mult (mult A B) C) =? (mult (mult A C) (ld C (mult B C))).
Axiom ax_f07 : forall A B C : Z, (mult A (mult B C)) =? (mult (rd (mult A B) A) (mult A C)).
Axiom ax_f06 : forall A : Z, (mult unit A) =? A.
Axiom ax_f05 : forall A : Z, (mult A unit) =? A.
Axiom ax_f04 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_f03 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_f02 : forall A B : Z, (ld A (mult A B)) =? B.
Axiom ax_f01 : forall A B : Z, (mult A (ld A B)) =? B.

Add_lemmas ax_goal1 ax_f08 ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01.

(* Goal *)
Theorem check : (mult (mult x1 x0) (mult x2 x3)) =? (mult (mult (mult x1 x0) x2) x3).
Proof.
  smt.
Qed.

Check check.

