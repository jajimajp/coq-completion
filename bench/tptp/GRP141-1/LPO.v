(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter greatest_lower_bound : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter least_upper_bound : G -> G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_glb1d_2 : (least_upper_bound b c) = b.
Axiom ax_glb1d_1 : (least_upper_bound a c) = a.
Axiom monotony_glb2 : forall X Y Z : G, (multiply (greatest_lower_bound Y Z) X) = (greatest_lower_bound (multiply Y X) (multiply Z X)).
Axiom monotony_lub2 : forall X Y Z : G, (multiply (least_upper_bound Y Z) X) = (least_upper_bound (multiply Y X) (multiply Z X)).
Axiom monotony_glb1 : forall X Y Z : G, (multiply X (greatest_lower_bound Y Z)) = (greatest_lower_bound (multiply X Y) (multiply X Z)).
Axiom monotony_lub1 : forall X Y Z : G, (multiply X (least_upper_bound Y Z)) = (least_upper_bound (multiply X Y) (multiply X Z)).
Axiom glb_absorbtion : forall X Y : G, (greatest_lower_bound X (least_upper_bound X Y)) = X.
Axiom lub_absorbtion : forall X Y : G, (least_upper_bound X (greatest_lower_bound X Y)) = X.
Axiom idempotence_of_gld : forall X : G, (greatest_lower_bound X X) = X.
Axiom idempotence_of_lub : forall X : G, (least_upper_bound X X) = X.
Axiom associativity_of_lub : forall X Y Z : G, (least_upper_bound X (least_upper_bound Y Z)) = (least_upper_bound (least_upper_bound X Y) Z).
Axiom associativity_of_glb : forall X Y Z : G, (greatest_lower_bound X (greatest_lower_bound Y Z)) = (greatest_lower_bound (greatest_lower_bound X Y) Z).
Axiom symmetry_of_lub : forall X Y : G, (least_upper_bound X Y) = (least_upper_bound Y X).
Axiom symmetry_of_glb : forall X Y : G, (greatest_lower_bound X Y) = (greatest_lower_bound Y X).
Axiom associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : G, (multiply identity X) = X.

Complete ax_glb1d_2 ax_glb1d_1 monotony_glb2 monotony_lub2 monotony_glb1 monotony_lub1 glb_absorbtion lub_absorbtion idempotence_of_gld idempotence_of_lub associativity_of_lub associativity_of_glb symmetry_of_lub symmetry_of_glb associativity left_inverse left_identity : a b c greatest_lower_bound identity inverse least_upper_bound multiply : hint
  for ((greatest_lower_bound (greatest_lower_bound a b) c) = c).

(* Goal *)
Theorem check : (greatest_lower_bound (greatest_lower_bound a b) c) = c.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

