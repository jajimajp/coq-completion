(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom multiply : forall X Y : Z, (multiply X Y) = (inverse (double_divide Y X)).
Axiom single_axiom : forall X Y Z : Z, (inverse (double_divide (inverse (double_divide (inverse (double_divide X Y)) Z)) (double_divide X Z))) = Y.

Add_lemmas multiply single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

