(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable asoc : Z -> Z -> Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom c09 : forall A B C : Z, (asoc A B C) = (ld (mult A (mult B C)) (mult (mult A B) C)).
Axiom c08 : forall A B C : Z, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom c07 : forall A B C : Z, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom c06 : forall A : Z, (mult unit A) = A.
Axiom c05 : forall A : Z, (mult A unit) = A.
Axiom c04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas c09 c08 c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (mult a (mult (asoc b c d) e)) = (mult (mult a (asoc b c d)) e).
Proof.
  smt.
Qed.

Check check.

