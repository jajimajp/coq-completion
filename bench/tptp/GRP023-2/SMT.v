(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_right_inverse : forall X : Z, (multiply X (inverse X)) =? identity.
Axiom ax_right_identity : forall X : Z, (multiply X identity) =? X.
Axiom ax_associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) =? (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : Z, (multiply (inverse X) X) =? identity.
Axiom ax_left_identity : forall X : Z, (multiply identity X) =? X.

Add_lemmas ax_right_inverse ax_right_identity ax_associativity ax_left_inverse ax_left_identity.

(* Goal *)
Theorem check : (inverse identity) =? identity.
Proof.
  smt.
Qed.

Check check.

