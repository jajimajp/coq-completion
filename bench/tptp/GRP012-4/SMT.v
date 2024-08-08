(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom right_inverse : forall X : Z, (multiply X (inverse X)) = identity.
Axiom right_identity : forall X : Z, (multiply X identity) = X.
Axiom associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : Z, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : Z, (multiply identity X) = X.

Add_lemmas right_inverse right_identity associativity left_inverse left_identity.

(* Goal *)
Theorem check : (inverse (multiply a b)) = (multiply (inverse b) (inverse a)).
Proof.
  smt.
Qed.

Check check.

