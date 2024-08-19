(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom moufang1 : forall X Y Z : G, (multiply (multiply X (multiply Y Z)) X) = (multiply (multiply X Y) (multiply Z X)).
Axiom left_inverse : forall X : G, (multiply (left_inverse X) X) = identity.
Axiom right_inverse : forall X : G, (multiply X (right_inverse X)) = identity.
Axiom right_division_multiply : forall X Y : G, (right_division (multiply X Y) Y) = X.
Axiom multiply_right_division : forall X Y : G, (multiply (right_division X Y) Y) = X.
Axiom left_division_multiply : forall X Y : G, (left_division X (multiply X Y)) = Y.
Axiom multiply_left_division : forall X Y : G, (multiply X (left_division X Y)) = Y.
Axiom right_identity : forall X : G, (multiply X identity) = X.
Axiom left_identity : forall X : G, (multiply identity X) = X.


(* Goal *)
Theorem check : (multiply (multiply (multiply a b) c) b) = (multiply a (multiply b (multiply c b))).
Proof.
  hammer.
Qed.

Check check.

