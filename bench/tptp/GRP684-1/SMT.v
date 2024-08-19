(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Axiom c07 : forall A B : Z, (ld A (mult A (ld B B))) = (rd (mult (rd A A) B) B).
Axiom c06 : forall A B C D : Z, (rd (mult (mult A B) (rd C D)) (rd C D)) = (mult A (rd (mult B D) D)).
Axiom c05 : forall A B C D : Z, (ld (ld A B) (mult (ld A B) (mult C D))) = (mult (ld A (mult A C)) D).
Axiom c04 : forall A B : Z, (mult (rd A B) B) = (rd (mult A B) B).
Axiom c03 : forall A B : Z, (mult A (ld A B)) = (ld A (mult A B)).
Axiom c02 : forall A : Z, (rd (mult A A) A) = A.
Axiom c01 : forall A : Z, (ld A (mult A A)) = A.

Add_lemmas c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (rd (mult a (mult b c)) (mult b c)) = (rd (mult a c) c).
Proof.
  smt.
Qed.

Check check.

