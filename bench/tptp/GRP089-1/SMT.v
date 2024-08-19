(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom inverse : forall X Z : Z, (inverse X) = (divide (divide Z Z) X).
Axiom multiply : forall X Y Z : Z, (multiply X Y) = (divide X (divide (divide Z Z) Y)).
Axiom single_axiom : forall X Y Z : Z, (divide X (divide (divide X Y) (divide Z Y))) = Z.

Add_lemmas inverse multiply single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

