(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom multiply : forall X Y : Z, (multiply X Y) = (divide X (inverse Y)).
Axiom single_axiom : forall X Y Z : Z, (divide (divide X (inverse (divide Y (divide X Z)))) Z) = Y.

Add_lemmas multiply single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

