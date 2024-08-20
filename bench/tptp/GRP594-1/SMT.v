(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a2 : Z.
Variable b2 : Z.
Variable double_divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_multiply : forall A B : Z, (multiply A B) = (inverse (double_divide B A)).
Axiom ax_single_axiom : forall A B C : Z, (inverse (double_divide (double_divide A B) (inverse (double_divide A (inverse (double_divide C B)))))) = C.

Add_lemmas ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  smt.
Qed.

Check check.

