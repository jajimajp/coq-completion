(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Axiom f05 : forall A B C : Z, (mult (mult A B) (mult C A)) = (mult (mult A (mult B C)) A).
Axiom f04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom f03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom f02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom f01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas f05 f04 f03 f02 f01.

(* Goal *)
Theorem check : forall X0 : Z, (tuple (mult X0 (x1 X0)) (mult (x1_2 X0) X0)) = (tuple (x1 X0) (x1_2 X0)).
Proof.
  smt.
Qed.

Check check.

