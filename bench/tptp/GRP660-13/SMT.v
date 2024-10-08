(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable x0 : Z.
Variable x1 : Z.
Axiom ax_f05 : forall A B C : Z, (mult (mult (mult A B) C) A) =? (mult A (mult B (mult C A))).
Axiom ax_f04 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_f03 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_f02 : forall A B : Z, (ld A (mult A B)) =? B.
Axiom ax_f01 : forall A B : Z, (mult A (ld A B)) =? B.

Add_lemmas ax_f05 ax_f04 ax_f03 ax_f02 ax_f01.

(* Goal *)
Theorem check : (mult x0 (ld x1 x1)) =? x0.
Proof.
  smt.
Qed.

Check check.

