(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom a_times_b_is_c : (multiply a b) = c.
Axiom squareness : forall X : Z, (multiply X X) = identity.
Axiom right_inverse : forall X : Z, (multiply X (inverse X)) = identity.
Axiom right_identity : forall X : Z, (multiply X identity) = X.
Axiom associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : Z, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : Z, (multiply identity X) = X.

Add_lemmas a_times_b_is_c squareness right_inverse right_identity associativity left_inverse left_identity.

(* Goal *)
Theorem check : (multiply b a) = c.
Proof.
  smt.
Qed.

Check check.

