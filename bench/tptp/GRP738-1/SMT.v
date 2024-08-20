(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom ax_c07 : forall A B C : Z, (ld A (mult (mult A B) C)) =? (rd (mult B (mult C A)) A).
Axiom ax_c06 : forall A : Z, (mult unit A) =? A.
Axiom ax_c05 : forall A : Z, (mult A unit) =? A.
Axiom ax_c04 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_c03 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_c02 : forall A B : Z, (ld A (mult A B)) =? B.
Axiom ax_c01 : forall A B : Z, (mult A (ld A B)) =? B.

Add_lemmas ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01.

(* Goal *)
Theorem check : (mult a (mult b c)) =? (mult (rd (mult a b) a) (mult a c)).
Proof.
  smt.
Qed.

Check check.

