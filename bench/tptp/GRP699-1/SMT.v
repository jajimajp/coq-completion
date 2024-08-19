(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom c08 : forall A B C : Z, (mult (mult A B) (mult B (mult C B))) = (mult (mult A (mult B (mult B C))) B).
Axiom c07 : forall A B C : Z, (mult (mult (mult A B) A) (mult A C)) = (mult A (mult (mult (mult B A) A) C)).
Axiom c06 : forall A : Z, (mult unit A) = A.
Axiom c05 : forall A : Z, (mult A unit) = A.
Axiom c04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas c08 c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (mult (mult a b) c) = (mult (mult a c) (ld c (mult b c))).
Proof.
  smt.
Qed.

Check check.

