(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Axiom ax_f05 : forall A B C : Z, (mult A (mult (mult B B) C)) = (mult (mult A B) (mult B C)).
Axiom ax_f04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas ax_f05 ax_f04 ax_f03 ax_f02 ax_f01.

(* Goal *)
Theorem check : (mult (mult a b) c) = (mult a (mult b c)).
Proof.
  smt.
Qed.

Check check.

