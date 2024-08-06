(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable op_c : Z.
Variable op_d : Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom c09 : forall A : Z, (mult op_d A) = (mult A op_d).
Axiom c08 : forall A : Z, (mult op_c A) = (mult A op_c).
Axiom c07 : forall A B C : Z, (mult A (mult B (mult A C))) = (mult (mult A (mult B A)) C).
Axiom c06 : forall A : Z, (mult unit A) = A.
Axiom c05 : forall A : Z, (mult A unit) = A.
Axiom c04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas c09 c08 c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (mult (mult (mult op_c op_c) op_d) a) = (mult a (mult (mult op_c op_c) op_d)).
Proof.
  smt.
Qed.

Check check.
