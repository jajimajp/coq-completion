(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom single_axiom : forall X Y Z : Z, (multiply X (multiply (multiply Y Z) (inverse (multiply X Z)))) = Y.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

