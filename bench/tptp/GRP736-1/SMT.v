(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Axiom c04 : forall A B : Z, (mult A (mult A (mult A B))) = B.
Axiom c03 : forall A B : Z, (mult (rd A B) B) = A.
Axiom c02 : forall A B : Z, (rd (mult A B) B) = A.
Axiom c01 : forall A B C : Z, (mult A (mult B C)) = (mult (mult A B) (mult A C)).

Add_lemmas c04 c03 c02 c01.

(* Goal *)
Theorem check : (mult (mult a b) (mult c d)) = (mult (mult a c) (mult b d)).
Proof.
  smt.
Qed.

Check check.

