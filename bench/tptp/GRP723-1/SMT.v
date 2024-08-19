(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom c09 : forall A B : Z, (f A B) = (ld B (ld (mult A B) B)).
Axiom c08 : forall A : Z, (mult A A) = unit.
Axiom c07 : forall A B C : Z, (ld A (mult (mult B C) A)) = (mult (ld A (mult B A)) (ld A (mult C A))).
Axiom c06 : forall A B C D : Z, (ld (mult A B) (mult A (mult B (mult C D)))) = (mult (ld (mult A B) (mult A (mult B C))) (ld (mult A B) (mult A (mult B D)))).
Axiom c05 : forall A B : Z, (mult A B) = (mult B A).
Axiom c04 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c03 : forall A B : Z, (mult A (ld A B)) = B.
Axiom c02 : forall A : Z, (mult unit A) = A.
Axiom c01 : forall A : Z, (mult A unit) = A.

Add_lemmas c09 c08 c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (f a (f b c)) = (f (f a b) c).
Proof.
  smt.
Qed.

Check check.

