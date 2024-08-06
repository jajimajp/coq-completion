(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable identity : Z.
Variable multiply : Z -> Z -> Z.
Axiom single_axiom : forall X Y Z : Z, (multiply X (multiply (multiply X (multiply (multiply X Y) Z)) (multiply identity (multiply Z Z)))) = Y.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply a identity) = a.
Proof.
  smt.
Qed.

Check check.
