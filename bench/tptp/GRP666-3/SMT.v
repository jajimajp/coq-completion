(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable i : Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom c11 : forall A B : Z, (mult (mult A B) (i B)) = A.
Axiom c10 : forall A B : Z, (mult (i A) (mult A B)) = B.
Axiom c09 : forall A B C : Z, (ld A (mult (mult B C) A)) = (mult (ld A (mult B A)) (ld A (mult C A))).
Axiom c08 : forall A B C D : Z, (rd (mult (mult (mult A B) C) D) (mult C D)) = (mult (rd (mult (mult A C) D) (mult C D)) (rd (mult (mult B C) D) (mult C D))).
Axiom c07 : forall A B C D : Z, (ld (mult A B) (mult A (mult B (mult C D)))) = (mult (ld (mult A B) (mult A (mult B C))) (ld (mult A B) (mult A (mult B D)))).
Axiom c06 : forall A : Z, (mult unit A) = A.
Axiom c05 : forall A : Z, (mult A unit) = A.
Axiom c04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas c11 c10 c09 c08 c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (mult a (mult b (mult c b))) = (mult (mult (mult a b) c) b).
Proof.
  smt.
Qed.

Check check.

