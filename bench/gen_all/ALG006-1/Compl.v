(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter difference : G -> G -> G.
Axiom set_difference_3 : forall X Y Z : G, (difference (difference X Y) Z) = (difference (difference X Z) (difference Y Z)).
Axiom set_difference_2 : forall X Y : G, (difference X (difference X Y)) = (difference Y (difference Y X)).
Axiom set_difference_1 : forall X Y : G, (difference X (difference Y X)) = X.

Complete set_difference_3 set_difference_2 set_difference_1 : difference : hint
  for ((difference (difference a c) b) = (difference (difference a b) c)).

(* Goal *)
Theorem check : (difference (difference a c) b) = (difference (difference a b) c).
Proof.
  autorewrite with hint.
  reflexivity.
Qed.

Check check.

