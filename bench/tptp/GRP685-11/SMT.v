(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Axiom f07 : forall A B : Z, (ld A (mult A (ld B B))) = (rd (mult (rd A A) B) B).
Axiom f06 : forall A B C D : Z, (rd (mult (mult A B) (rd C D)) (rd C D)) = (mult A (rd (mult B D) D)).
Axiom f05 : forall A B C D : Z, (ld (ld A B) (mult (ld A B) (mult C D))) = (mult (ld A (mult A C)) D).
Axiom f04 : forall A B : Z, (mult (rd A B) B) = (rd (mult A B) B).
Axiom f03 : forall A B : Z, (mult A (ld A B)) = (ld A (mult A B)).
Axiom f02 : forall A : Z, (rd (mult A A) A) = A.
Axiom f01 : forall A : Z, (ld A (mult A A)) = A.

Add_lemmas f07 f06 f05 f04 f03 f02 f01.

(* Goal *)
Theorem check : (rd (mult x6 (rd x7 x8)) (rd x7 x8)) = (rd (mult x6 x8) x8).
Proof.
  smt.
Qed.

Check check.
