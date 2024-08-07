(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable double_divide : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom identity : forall A : Z, identity = (double_divide A (inverse A)).
Axiom inverse : forall A : Z, (inverse A) = (double_divide A identity).
Axiom multiply : forall A B : Z, (multiply A B) = (double_divide (double_divide B A) identity).
Axiom single_axiom : forall A B C D : Z, (double_divide (double_divide (double_divide A (double_divide B identity)) (double_divide (double_divide C (double_divide D (double_divide D identity))) (double_divide A identity))) B) = C.

Add_lemmas identity inverse multiply single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  smt.
Qed.

Check check.

