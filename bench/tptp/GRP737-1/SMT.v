(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable d : Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Axiom ax_c04 : forall A B : Z, (mult A (mult A B)) =? B.
Axiom ax_c03 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_c02 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_c01 : forall A B C : Z, (mult A (mult B C)) =? (mult (mult A B) (mult A C)).

Add_lemmas ax_c04 ax_c03 ax_c02 ax_c01.

(* Goal *)
Theorem check : (mult (mult a b) (mult c d)) =? (mult (mult a c) (mult b d)).
Proof.
  smt.
Qed.

Check check.

