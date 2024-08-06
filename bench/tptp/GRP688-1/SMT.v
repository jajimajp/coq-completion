(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable i : Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable op_c : Z.
Variable op_d : Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom c11 : (mult op_d (mult op_d op_d)) = unit.
Axiom c10 : (mult op_c (mult op_c (mult op_c op_c))) = unit.
Axiom c09 : forall A B : Z, (i (mult A B)) = (mult (i A) (i B)).
Axiom c08 : forall A B : Z, (mult (i A) (mult A B)) = B.
Axiom c07 : forall A B C : Z, (mult A (mult B (mult A C))) = (mult (mult A (mult B A)) C).
Axiom c06 : forall A : Z, (mult unit A) = A.
Axiom c05 : forall A : Z, (mult A unit) = A.
Axiom c04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas c11 c10 c09 c08 c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (mult op_c op_d) = (mult op_d op_c).
Proof.
  smt.
Qed.

Check check.

