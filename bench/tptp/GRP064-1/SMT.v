(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a1 : Z.
Variable a2 : Z.
Variable a3 : Z.
Variable b1 : Z.
Variable b2 : Z.
Variable b3 : Z.
Variable c3 : Z.
Variable divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_inverse : forall X Z : Z, (inverse X) =? (divide (divide Z Z) X).
Axiom ax_multiply : forall X Y Z : Z, (multiply X Y) =? (divide X (divide (divide Z Z) Y)).
Axiom ax_single_axiom : forall X Y Z : Z, (divide X (divide (divide (divide (divide Y Y) Y) Z) (divide (divide (divide Y Y) X) Z))) =? Y.

Add_lemmas ax_inverse ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) =? (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

