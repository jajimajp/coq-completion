(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable f : Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom ax_c09 : forall A : Z, (mult (f A) (f A)) =? A.
Axiom ax_c08 : forall A B : Z, (mult (mult A B) A) =? (mult A (mult B A)).
Axiom ax_c07 : forall A B C : Z, (mult (mult A B) (mult (mult C B) C)) =? (mult (mult A (mult (mult B C) B)) C).
Axiom ax_c06 : forall A : Z, (mult unit A) =? A.
Axiom ax_c05 : forall A : Z, (mult A unit) =? A.
Axiom ax_c04 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_c03 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_c02 : forall A B : Z, (ld A (mult A B)) =? B.
Axiom ax_c01 : forall A B : Z, (mult A (ld A B)) =? B.

Add_lemmas ax_c09 ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01.

(* Goal *)
Theorem check : (mult (mult a b) (mult c a)) =? (mult a (mult (mult b c) a)).
Proof.
  smt.
Qed.

Check check.

