(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a1 : Z.
Variable double_divide : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_identity : forall A : Z, identity =? (double_divide A (inverse A)).
Axiom ax_inverse : forall A : Z, (inverse A) =? (double_divide A identity).
Axiom ax_multiply : forall A B : Z, (multiply A B) =? (double_divide (double_divide B A) identity).
Axiom ax_single_axiom : forall A B C : Z, (double_divide (double_divide identity A) (double_divide identity (double_divide (double_divide (double_divide A B) identity) (double_divide C B)))) =? C.

Add_lemmas ax_identity ax_inverse ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) =? identity.
Proof.
  smt.
Qed.

Check check.

