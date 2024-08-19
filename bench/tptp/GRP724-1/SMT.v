(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom c20 : forall A B C : Z, (op_l (op_l A B C) B C) = A.
Axiom c19 : forall A B C : Z, (op_r (op_r A B C) B C) = A.
Axiom c18 : forall A B : Z, (op_t (op_t A B) B) = A.
Axiom c17 : forall A B C : Z, (op_t (op_t A B) C) = (op_t (op_t A C) B).
Axiom c16 : forall A B C D : Z, (op_t (op_l A B C) D) = (op_l (op_t A D) B C).
Axiom c15 : forall A B C D : Z, (op_t (op_r A B C) D) = (op_r (op_t A D) B C).
Axiom c14 : forall A B C D E : Z, (op_l (op_l A B C) D E) = (op_l (op_l A D E) B C).
Axiom c13 : forall A B C D E : Z, (op_l (op_r A B C) D E) = (op_r (op_l A D E) B C).
Axiom c12 : forall A B C D E : Z, (op_r (op_r A B C) D E) = (op_r (op_r A D E) B C).
Axiom c11 : forall A B : Z, (op_t A B) = (ld B (mult A B)).
Axiom c10 : forall A B C : Z, (op_r A B C) = (rd (mult (mult A B) C) (mult B C)).
Axiom c09 : forall A B C : Z, (op_l A B C) = (ld (mult C B) (mult C (mult B A))).
Axiom c08 : forall A : Z, (s (mult A A)) = A.
Axiom c07 : forall A : Z, (mult (s A) (s A)) = A.
Axiom c06 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c05 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c04 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c03 : forall A B : Z, (mult A (ld A B)) = B.
Axiom c02 : forall A : Z, (mult A unit) = A.
Axiom c01 : forall A : Z, (mult unit A) = A.

Add_lemmas c20 c19 c18 c17 c16 c15 c14 c13 c12 c11 c10 c09 c08 c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (mult (mult a b) c) = (mult a (mult b c)).
Proof.
  smt.
Qed.

Check check.

