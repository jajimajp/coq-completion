(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom identity : forall A : Z, identity = (double_divide A (inverse A)).
Axiom inverse : forall A : Z, (inverse A) = (double_divide A identity).
Axiom multiply : forall A B : Z, (multiply A B) = (double_divide (double_divide B A) identity).
Axiom single_axiom : forall A B C : Z, (double_divide A (double_divide (double_divide (double_divide identity (double_divide (double_divide A identity) (double_divide B C))) B) identity)) = C.

Add_lemmas identity inverse multiply single_axiom.

(* Goal *)
Theorem check : (multiply identity a2) = a2.
Proof.
  smt.
Qed.

Check check.

