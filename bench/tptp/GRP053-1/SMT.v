(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom single_axiom : forall X Y Z : Z, (inverse (multiply Y (inverse (multiply (inverse (multiply (inverse (multiply Z Y)) (multiply Z (inverse X)))) (inverse (multiply (inverse Y) Y)))))) = X.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

