(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable identity : Z.
Variable left_division : Z -> Z -> Z.
Variable left_inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Variable right_division : Z -> Z -> Z.
Variable right_inverse : Z -> Z.
Axiom moufang3 : forall X Y Z : Z, (multiply (multiply (multiply X Y) X) Z) = (multiply X (multiply Y (multiply X Z))).
Axiom left_inverse : forall X : Z, (multiply (left_inverse X) X) = identity.
Axiom right_inverse : forall X : Z, (multiply X (right_inverse X)) = identity.
Axiom right_division_multiply : forall X Y : Z, (right_division (multiply X Y) Y) = X.
Axiom multiply_right_division : forall X Y : Z, (multiply (right_division X Y) Y) = X.
Axiom left_division_multiply : forall X Y : Z, (left_division X (multiply X Y)) = Y.
Axiom multiply_left_division : forall X Y : Z, (multiply X (left_division X Y)) = Y.
Axiom right_identity : forall X : Z, (multiply X identity) = X.
Axiom left_identity : forall X : Z, (multiply identity X) = X.

Add_lemmas moufang3 left_inverse right_inverse right_division_multiply multiply_right_division left_division_multiply multiply_left_division right_identity left_identity.

(* Goal *)
Theorem check : (multiply (multiply a (multiply b c)) a) = (multiply (multiply a b) (multiply c a)).
Proof.
  smt.
Qed.

Check check.

