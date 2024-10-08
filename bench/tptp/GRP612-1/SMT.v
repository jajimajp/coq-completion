(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable double_divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_multiply : forall A B : Z, (multiply A B) =? (inverse (double_divide B A)).
Axiom ax_single_axiom : forall A B C : Z, (inverse (double_divide (inverse (double_divide (inverse (double_divide A B)) C)) (double_divide A C))) =? B.

Add_lemmas ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply a b) =? (multiply b a).
Proof.
  smt.
Qed.

Check check.

