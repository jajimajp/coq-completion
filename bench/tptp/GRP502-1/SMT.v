(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a1 : Z.
Variable b1 : Z.
Variable double_divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_multiply : forall A B : Z, (multiply A B) = (inverse (double_divide B A)).
Axiom ax_single_axiom : forall A B C D : Z, (double_divide (double_divide A (inverse (double_divide B C))) (double_divide (inverse B) (inverse (double_divide D (double_divide A D))))) = C.

Add_lemmas ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

