(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable f : Z -> Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable unit : Z.
Axiom ax_c08 : forall A B : Z, (mult (mult A A) (mult B B)) =? (mult (f A B) (f A B)).
Axiom ax_c07 : forall A B C : Z, (ld A (mult (mult B C) A)) =? (mult (ld A (mult B A)) (ld A (mult C A))).
Axiom ax_c06 : forall A B C D : Z, (ld (mult A B) (mult A (mult B (mult C D)))) =? (mult (ld (mult A B) (mult A (mult B C))) (ld (mult A B) (mult A (mult B D)))).
Axiom ax_c05 : forall A B : Z, (mult A B) =? (mult B A).
Axiom ax_c04 : forall A B : Z, (ld A (mult A B)) =? B.
Axiom ax_c03 : forall A B : Z, (mult A (ld A B)) =? B.
Axiom ax_c02 : forall A : Z, (mult unit A) =? A.
Axiom ax_c01 : forall A : Z, (mult A unit) =? A.

Add_lemmas ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01.

(* Goal *)
Theorem check : (f a b) =? (f b a).
Proof.
  smt.
Qed.

Check check.

