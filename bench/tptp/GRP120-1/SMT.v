(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom single_axiom2 : (multiply identity identity) = identity.
Axiom single_axiom : forall X Y Z : Z, (multiply Y (multiply (multiply Y (multiply (multiply Y Y) (multiply X Z))) (multiply Z (multiply Z Z)))) = X.

Add_lemmas single_axiom2 single_axiom.

(* Goal *)
Theorem check : (multiply identity a) = a.
Proof.
  smt.
Qed.

Check check.

