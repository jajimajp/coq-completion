(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable i : Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom c11 : forall A : Z, (mult A (i A)) = unit.
Axiom c10 : forall A : Z, (mult (i A) A) = unit.
Axiom c09 : forall A B C : Z, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom c08 : forall A B C : Z, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom c07 : forall A B : Z, (mult A (i (mult B A))) = (i B).
Axiom c06 : forall A : Z, (mult unit A) = A.
Axiom c05 : forall A : Z, (mult A unit) = A.
Axiom c04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas c11 c10 c09 c08 c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (mult (mult a b) (mult b (mult c b))) = (mult (mult a (mult b (mult b c))) b).
Proof.
  smt.
Qed.

Check check.

