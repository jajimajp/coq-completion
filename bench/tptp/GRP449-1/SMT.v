(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom inverse : forall A B : Z, (inverse A) = (divide (divide B B) A).
Axiom multiply : forall A B C : Z, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom single_axiom : forall A B C : Z, (divide A (divide (divide (divide (divide B B) B) C) (divide (divide (divide B B) A) C))) = B.

Add_lemmas inverse multiply single_axiom.

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  smt.
Qed.

Check check.

