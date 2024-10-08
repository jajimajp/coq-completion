(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable f : Z -> Z.
Variable ifeq : Z -> Z -> Z -> Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom ax_f12 : forall X6 X7 X8 : Z, (ifeq (mult (mult X6 X7) (mult X8 X6)) (mult X6 (mult (mult X7 X8) X6)) (mult X6 (mult X7 (mult X6 X8))) (mult (mult (mult X6 X7) X6) X8)) =? (mult (mult (mult X6 X7) X6) X8).
Axiom ax_f11 : forall X3 X4 X5 : Z, (ifeq (mult (mult X3 X4) (mult X5 X3)) (mult (mult X3 (mult X4 X5)) X3) (mult X3 (mult X4 (mult X3 X5))) (mult (mult (mult X3 X4) X3) X5)) =? (mult (mult (mult X3 X4) X3) X5).
Axiom ax_f10 : forall X0 X1 X2 : Z, (ifeq (mult X0 (mult X1 (mult X2 X1))) (mult (mult (mult X0 X1) X2) X1) (mult X1 (mult X0 (mult X1 X2))) (mult (mult (mult X1 X0) X1) X2)) =? (mult (mult (mult X1 X0) X1) X2).
Axiom ax_f09 : forall A : Z, (mult (f A) (f A)) =? A.
Axiom ax_f08 : forall A B : Z, (mult (mult A B) A) =? (mult A (mult B A)).
Axiom ax_f07 : forall A B C : Z, (mult (mult A B) (mult (mult C B) C)) =? (mult (mult A (mult (mult B C) B)) C).
Axiom ax_f06 : forall A : Z, (mult unit A) =? A.
Axiom ax_f05 : forall A : Z, (mult A unit) =? A.
Axiom ax_f04 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_f03 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_f02 : forall A B : Z, (ld A (mult A B)) =? B.
Axiom ax_f01 : forall A B : Z, (mult A (ld A B)) =? B.
Axiom ax_ifeq_axiom : forall A B C : Z, (ifeq A A B C) =? B.

Add_lemmas ax_f12 ax_f11 ax_f10 ax_f09 ax_f08 ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 ax_ifeq_axiom.

(* Goal *)
Theorem check : (mult a (mult b (mult a c))) =? (mult (mult (mult a b) a) c).
Proof.
  smt.
Qed.

Check check.

