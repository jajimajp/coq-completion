(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable f : Z -> Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable op_c : Z.
Variable rd : Z -> Z -> Z.
Axiom c07 : forall A B : Z, (f A B) = (mult (rd A op_c) (ld op_c B)).
Axiom c06 : forall A B C : Z, (mult (mult A B) C) = (mult (mult A (rd C C)) (mult B C)).
Axiom c05 : forall A B C : Z, (mult A (mult B C)) = (mult (mult A B) (mult (ld A A) C)).
Axiom c04 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c02 : forall A B : Z, (ld A (mult A B)) = B.
Axiom c01 : forall A B : Z, (mult A (ld A B)) = B.

Add_lemmas c07 c06 c05 c04 c03 c02 c01.

(* Goal *)
Theorem check : (f a (f b (f a c))) = (f (f (f a b) a) c).
Proof.
  smt.
Qed.

Check check.

