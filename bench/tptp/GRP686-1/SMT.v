(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom c07 : forall A B C : Z, (mult A (mult B (mult B C))) = (mult (mult A (mult B B)) C).
Axiom c06 : forall A : Z, (mult unit A) = A.
Axiom c05 : forall A : Z, (mult A unit) = A.
Axiom c04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (mult (mult a a) (mult b c)) = (mult (mult a (mult a b)) c).
Proof.
  smt.
Qed.

Check check.

