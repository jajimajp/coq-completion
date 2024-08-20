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
Axiom ax_inverse : forall A : Z, (inverse A) = (divide identity A).
Axiom ax_multiply : forall A B : Z, (multiply A B) = (divide A (divide identity B)).
Axiom ax_single_axiom : forall A B C : Z, (divide (divide identity (divide A B)) (divide (divide B C) A)) = C.

Add_lemmas ax_identity ax_inverse ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

