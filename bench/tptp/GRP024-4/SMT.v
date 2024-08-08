(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable commutator : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom commutator : forall X Y : Z, (commutator X Y) = (multiply X (multiply Y (multiply (inverse X) (inverse Y)))).
Axiom right_inverse : forall X : Z, (multiply X (inverse X)) = identity.
Axiom right_identity : forall X : Z, (multiply X identity) = X.
Axiom associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : Z, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : Z, (multiply identity X) = X.

Add_lemmas commutator right_inverse right_identity associativity left_inverse left_identity.

(* Goal *)
Theorem check : (commutator (commutator a b) c) = (commutator a (commutator b c)).
Proof.
  smt.
Qed.

Check check.

