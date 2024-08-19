(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom inverse : forall X Z : Z, (inverse X) = (divide (divide Z Z) X).
Axiom multiply : forall X Y Z : Z, (multiply X Y) = (divide X (divide (divide Z Z) Y)).
Axiom single_axiom : forall X Y Z : Z, (divide X (divide (divide (divide (divide X X) Y) Z) (divide (divide (divide X X) X) Z))) = Y.

Add_lemmas inverse multiply single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

