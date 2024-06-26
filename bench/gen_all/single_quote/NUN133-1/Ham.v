(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter cubes : G -> G.
Parameter one : G.
Parameter s : G -> G.
Parameter sum : G -> G.
Parameter times : G -> G -> G.
Parameter zero : G.
Axiom induction_hypothesis : (times (sum a) (sum a)) = (cubes a).
Axiom plus_sum : forall '+' N : G, ('+' (sum N) (sum N)) = (times N (s N)).
Axiom cubes_s : forall '+' N : G, (cubes (s N)) = ('+' (times (s N) (times (s N) (s N))) (cubes N)).
Axiom cubes_zero : (cubes zero) = zero.
Axiom sum_s : forall '+' N : G, (sum (s N)) = ('+' (s N) (sum N)).
Axiom sum_zero : (sum zero) = zero.
Axiom times_s : forall '+' X Y : G, (times (s X) Y) = ('+' Y (times X Y)).
Axiom plus_s : forall '+' X Y : G, ('+' (s X) Y) = (s ('+' X Y)).
Axiom distr_001 : forall '+' X Y Z : G, (times ('+' X Y) Z) = ('+' (times X Z) (times Y Z)).
Axiom distr : forall '+' X Y Z : G, (times X ('+' Y Z)) = ('+' (times X Y) (times X Z)).
Axiom times_one : forall X : G, (times X one) = X.
Axiom times_zero : forall X : G, (times X zero) = zero.
Axiom plus_zero : forall '+' X : G, ('+' X zero) = X.
Axiom times_assoc : forall X Y Z : G, (times X (times Y Z)) = (times (times X Y) Z).
Axiom times_comm : forall X Y : G, (times X Y) = (times Y X).
Axiom plus_assoc : forall '+' X Y Z : G, ('+' X ('+' Y Z)) = ('+' ('+' X Y) Z).
Axiom plus_comm : forall '+' X Y : G, ('+' X Y) = ('+' Y X).


(* Goal *)
Theorem check : (times (sum (s a)) (sum (s a))) = (cubes (s a)).
Proof.
  hammer.
Qed.

Check check.

