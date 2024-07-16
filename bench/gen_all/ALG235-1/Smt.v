(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable mult : Z -> Z -> Z.
Axiom c03 : forall A B C D : Z, (mult (mult A (mult B (mult C B))) D) =? (mult A (mult D (mult (mult C B) D))).
Axiom c02 : forall A B C D : Z, (mult A (mult B (mult C D))) =? (mult C (mult B (mult A D))).
Axiom c01 : forall A B : Z, (mult A (mult B (mult A B))) =? (mult A B).

Add_lemmas c03 c02 c01.

(* Zoal *)
Theorem check : (mult a (mult b (mult a (mult c (mult d c))))) =? (mult a (mult b (mult d c))).
Proof.
  smt.
Qed.

Check check.

