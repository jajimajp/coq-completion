(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter greatest_lower_bound : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter least_upper_bound : G -> G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_monotony_glb2 : forall X Y Z : G, (multiply (greatest_lower_bound Y Z) X) = (greatest_lower_bound (multiply Y X) (multiply Z X)).
Axiom ax_monotony_lub2 : forall X Y Z : G, (multiply (least_upper_bound Y Z) X) = (least_upper_bound (multiply Y X) (multiply Z X)).
Axiom ax_monotony_glb1 : forall X Y Z : G, (multiply X (greatest_lower_bound Y Z)) = (greatest_lower_bound (multiply X Y) (multiply X Z)).
Axiom ax_monotony_lub1 : forall X Y Z : G, (multiply X (least_upper_bound Y Z)) = (least_upper_bound (multiply X Y) (multiply X Z)).
Axiom ax_glb_absorbtion : forall X Y : G, (greatest_lower_bound X (least_upper_bound X Y)) = X.
Axiom ax_lub_absorbtion : forall X Y : G, (least_upper_bound X (greatest_lower_bound X Y)) = X.
Axiom ax_idempotence_of_gld : forall X : G, (greatest_lower_bound X X) = X.
Axiom ax_idempotence_of_lub : forall X : G, (least_upper_bound X X) = X.
Axiom ax_associativity_of_lub : forall X Y Z : G, (least_upper_bound X (least_upper_bound Y Z)) = (least_upper_bound (least_upper_bound X Y) Z).
Axiom ax_associativity_of_glb : forall X Y Z : G, (greatest_lower_bound X (greatest_lower_bound Y Z)) = (greatest_lower_bound (greatest_lower_bound X Y) Z).
Axiom ax_symmetry_of_lub : forall X Y : G, (least_upper_bound X Y) = (least_upper_bound Y X).
Axiom ax_symmetry_of_glb : forall X Y : G, (greatest_lower_bound X Y) = (greatest_lower_bound Y X).
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.

Complete ax_monotony_glb2 ax_monotony_lub2 ax_monotony_glb1 ax_monotony_lub1 ax_glb_absorbtion ax_lub_absorbtion ax_idempotence_of_gld ax_idempotence_of_lub ax_associativity_of_lub ax_associativity_of_glb ax_symmetry_of_lub ax_symmetry_of_glb ax_associativity ax_left_inverse ax_left_identity : a b greatest_lower_bound identity inverse least_upper_bound multiply : hint
  for ((least_upper_bound (least_upper_bound (multiply a b) identity) (multiply (least_upper_bound a identity) (least_upper_bound b identity))) = (multiply (least_upper_bound a identity) (least_upper_bound b identity))).

(* Goal *)
Theorem check : (least_upper_bound (least_upper_bound (multiply a b) identity) (multiply (least_upper_bound a identity) (least_upper_bound b identity))) = (multiply (least_upper_bound a identity) (least_upper_bound b identity)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

