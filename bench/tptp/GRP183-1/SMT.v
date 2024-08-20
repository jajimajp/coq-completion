(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable greatest_lower_bound : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable least_upper_bound : Z -> Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_monotony_glb2 : forall X Y Z : Z, (multiply (greatest_lower_bound Y Z) X) = (greatest_lower_bound (multiply Y X) (multiply Z X)).
Axiom ax_monotony_lub2 : forall X Y Z : Z, (multiply (least_upper_bound Y Z) X) = (least_upper_bound (multiply Y X) (multiply Z X)).
Axiom ax_monotony_glb1 : forall X Y Z : Z, (multiply X (greatest_lower_bound Y Z)) = (greatest_lower_bound (multiply X Y) (multiply X Z)).
Axiom ax_monotony_lub1 : forall X Y Z : Z, (multiply X (least_upper_bound Y Z)) = (least_upper_bound (multiply X Y) (multiply X Z)).
Axiom ax_glb_absorbtion : forall X Y : Z, (greatest_lower_bound X (least_upper_bound X Y)) = X.
Axiom ax_lub_absorbtion : forall X Y : Z, (least_upper_bound X (greatest_lower_bound X Y)) = X.
Axiom ax_idempotence_of_gld : forall X : Z, (greatest_lower_bound X X) = X.
Axiom ax_idempotence_of_lub : forall X : Z, (least_upper_bound X X) = X.
Axiom ax_associativity_of_lub : forall X Y Z : Z, (least_upper_bound X (least_upper_bound Y Z)) = (least_upper_bound (least_upper_bound X Y) Z).
Axiom ax_associativity_of_glb : forall X Y Z : Z, (greatest_lower_bound X (greatest_lower_bound Y Z)) = (greatest_lower_bound (greatest_lower_bound X Y) Z).
Axiom ax_symmetry_of_lub : forall X Y : Z, (least_upper_bound X Y) = (least_upper_bound Y X).
Axiom ax_symmetry_of_glb : forall X Y : Z, (greatest_lower_bound X Y) = (greatest_lower_bound Y X).
Axiom ax_associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : Z, (multiply (inverse X) X) = identity.
Axiom ax_left_identity : forall X : Z, (multiply identity X) = X.

Add_lemmas ax_monotony_glb2 ax_monotony_lub2 ax_monotony_glb1 ax_monotony_lub1 ax_glb_absorbtion ax_lub_absorbtion ax_idempotence_of_gld ax_idempotence_of_lub ax_associativity_of_lub ax_associativity_of_glb ax_symmetry_of_lub ax_symmetry_of_glb ax_associativity ax_left_inverse ax_left_identity.

(* Goal *)
Theorem check : (greatest_lower_bound (least_upper_bound a identity) (inverse (greatest_lower_bound a identity))) = identity.
Proof.
  smt.
Qed.

Check check.

