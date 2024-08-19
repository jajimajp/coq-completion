(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom p12x_4 : forall X Y : G, (inverse (least_upper_bound X Y)) = (greatest_lower_bound (inverse X) (inverse Y)).
Axiom p12x_3 : forall X Y : G, (inverse (greatest_lower_bound X Y)) = (least_upper_bound (inverse X) (inverse Y)).
Axiom p12x_2 : (least_upper_bound a c) = (least_upper_bound b c).
Axiom p12x_1 : (greatest_lower_bound a c) = (greatest_lower_bound b c).
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


(* Goal *)
Theorem check : a = b.
Proof.
  hammer.
Qed.

Check check.

