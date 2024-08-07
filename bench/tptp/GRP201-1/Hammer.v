(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter identity : G.
Parameter left_division : G -> G -> G.
Parameter left_inverse : G -> G.
Parameter multiply : G -> G -> G.
Parameter right_division : G -> G -> G.
Parameter right_inverse : G -> G.
Axiom moufang2 : forall X Y Z : G, (multiply (multiply (multiply X Y) Z) Y) = (multiply X (multiply Y (multiply Z Y))).
Axiom left_inverse : forall X : G, (multiply (left_inverse X) X) = identity.
Axiom right_inverse : forall X : G, (multiply X (right_inverse X)) = identity.
Axiom right_division_multiply : forall X Y : G, (right_division (multiply X Y) Y) = X.
Axiom multiply_right_division : forall X Y : G, (multiply (right_division X Y) Y) = X.
Axiom left_division_multiply : forall X Y : G, (left_division X (multiply X Y)) = Y.
Axiom multiply_left_division : forall X Y : G, (multiply X (left_division X Y)) = Y.
Axiom right_identity : forall X : G, (multiply X identity) = X.
Axiom left_identity : forall X : G, (multiply identity X) = X.


(* Goal *)
Theorem check : (multiply (multiply (multiply a b) a) c) = (multiply a (multiply b (multiply a c))).
Proof.
  hammer.
Qed.

Check check.

