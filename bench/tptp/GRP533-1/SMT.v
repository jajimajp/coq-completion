(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a1 : Z.
Variable b1 : Z.
Variable divide : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_identity : forall A : Z, identity = (divide A A).
Axiom ax_inverse : forall A B : Z, (inverse A) = (divide (divide B B) A).
Axiom ax_multiply : forall A B C : Z, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom ax_single_axiom : forall A B C : Z, (divide (divide A (divide (divide A B) C)) B) = C.

Add_lemmas ax_identity ax_inverse ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

