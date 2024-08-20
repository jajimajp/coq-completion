(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable i : Z -> Z.
Variable mult : Z -> Z -> Z.
Variable unit : Z.
Variable x0 : Z.
Variable x1 : Z.
Axiom ax_f05 : forall A : Z, (mult (i A) A) =? unit.
Axiom ax_f04 : forall A : Z, (mult A (i A)) =? unit.
Axiom ax_f03 : forall A B C : Z, (mult A (mult B (mult B C))) =? (mult (mult (mult A B) B) C).
Axiom ax_f02 : forall A : Z, (mult unit A) =? A.
Axiom ax_f01 : forall A : Z, (mult A unit) =? A.

Add_lemmas ax_f05 ax_f04 ax_f03 ax_f02 ax_f01.

(* Goal *)
Theorem check : forall X2 : Z, (mult x0 X2) =? x1.
Proof.
  smt.
Qed.

Check check.

