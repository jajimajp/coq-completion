(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom f05 : forall A B C : Z, (mult A (mult B (mult C B))) = (mult (mult (mult A B) C) B).
Axiom f04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom f03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom f02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom f01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas f05 f04 f03 f02 f01.

(* Goal *)
Theorem check : (mult x0 (ld x1 x1)) = x0.
Proof.
  smt.
Qed.

Check check.

