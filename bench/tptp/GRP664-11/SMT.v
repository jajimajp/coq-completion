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
Axiom goal1 : (mult x0 x1) = unit.
Axiom f08 : forall A B C : Z, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom f07 : forall A B C : Z, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom f06 : forall A : Z, (mult unit A) = A.
Axiom f05 : forall A : Z, (mult A unit) = A.
Axiom f04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom f03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom f02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom f01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas goal1 f08 f07 f06 f05 f04 f03 f02 f01.

(* Goal *)
Theorem check : (mult (mult x2 (mult x1 x0)) x3) = (mult x2 (mult (mult x1 x0) x3)).
Proof.
  smt.
Qed.

Check check.

