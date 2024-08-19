(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable greatest_lower_bound : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable least_upper_bound : Z -> Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom p08a_3 : (least_upper_bound identity c) = c.
Axiom p08a_2 : (least_upper_bound identity b) = b.
Axiom p08a_1 : (least_upper_bound identity a) = a.
Axiom monotony_glb2 : forall X Y Z : Z, (multiply (greatest_lower_bound Y Z) X) = (greatest_lower_bound (multiply Y X) (multiply Z X)).
Axiom monotony_lub2 : forall X Y Z : Z, (multiply (least_upper_bound Y Z) X) = (least_upper_bound (multiply Y X) (multiply Z X)).
Axiom monotony_glb1 : forall X Y Z : Z, (multiply X (greatest_lower_bound Y Z)) = (greatest_lower_bound (multiply X Y) (multiply X Z)).
Axiom monotony_lub1 : forall X Y Z : Z, (multiply X (least_upper_bound Y Z)) = (least_upper_bound (multiply X Y) (multiply X Z)).
Axiom glb_absorbtion : forall X Y : Z, (greatest_lower_bound X (least_upper_bound X Y)) = X.
Axiom lub_absorbtion : forall X Y : Z, (least_upper_bound X (greatest_lower_bound X Y)) = X.
Axiom idempotence_of_gld : forall X : Z, (greatest_lower_bound X X) = X.
Axiom idempotence_of_lub : forall X : Z, (least_upper_bound X X) = X.
Axiom associativity_of_lub : forall X Y Z : Z, (least_upper_bound X (least_upper_bound Y Z)) = (least_upper_bound (least_upper_bound X Y) Z).
Axiom associativity_of_glb : forall X Y Z : Z, (greatest_lower_bound X (greatest_lower_bound Y Z)) = (greatest_lower_bound (greatest_lower_bound X Y) Z).
Axiom symmetry_of_lub : forall X Y : Z, (least_upper_bound X Y) = (least_upper_bound Y X).
Axiom symmetry_of_glb : forall X Y : Z, (greatest_lower_bound X Y) = (greatest_lower_bound Y X).
Axiom associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : Z, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : Z, (multiply identity X) = X.

Add_lemmas p08a_3 p08a_2 p08a_1 monotony_glb2 monotony_lub2 monotony_glb1 monotony_lub1 glb_absorbtion lub_absorbtion idempotence_of_gld idempotence_of_lub associativity_of_lub associativity_of_glb symmetry_of_lub symmetry_of_glb associativity left_inverse left_identity.

(* Goal *)
Theorem check : (least_upper_bound (greatest_lower_bound a (multiply b c)) (multiply (greatest_lower_bound a b) (greatest_lower_bound a c))) = (multiply (greatest_lower_bound a b) (greatest_lower_bound a c)).
Proof.
  smt.
Qed.

Check check.

