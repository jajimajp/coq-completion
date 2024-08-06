(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable identity : Z.
Variable multiply : Z -> Z -> Z.
Axiom single_axiom2 : (multiply identity identity) = identity.
Axiom single_axiom : forall X Y Z : Z, (multiply Y (multiply (multiply Y (multiply (multiply Y Y) (multiply X Z))) (multiply Z (multiply Z Z)))) = X.

Add_lemmas single_axiom2 single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a b) c) = (multiply a (multiply b c)).
Proof.
  smt.
Qed.

Check check.
