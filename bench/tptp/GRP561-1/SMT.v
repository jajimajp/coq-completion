(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a1 : Z.
Variable b1 : Z.
Variable divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_multiply : forall A B : Z, (multiply A B) =? (divide A (inverse B)).
Axiom ax_single_axiom : forall A B C : Z, (divide (divide (divide A (inverse B)) C) (divide A C)) =? B.

Add_lemmas ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) =? (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

