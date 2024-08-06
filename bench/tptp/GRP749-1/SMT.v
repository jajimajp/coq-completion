(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Axiom f06 : forall A B C : Z, (mult (mult A A) (mult B C)) = (mult (mult A B) (mult A C)).
Axiom f05 : forall A B C : Z, (mult (mult A (mult A A)) (mult B C)) = (mult (mult A B) (mult (mult A A) C)).
Axiom f04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom f03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom f02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom f01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas f06 f05 f04 f03 f02 f01.

(* Goal *)
Theorem check : (mult (mult a b) (mult c c)) = (mult (mult a c) (mult b c)).
Proof.
  smt.
Qed.

Check check.

