(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter cos : G -> G.
Parameter d : G -> G.
Parameter minus : G -> G.
Parameter one : G.
Parameter sin : G -> G.
Parameter times : G -> G -> G.
Parameter x : G.
Parameter zero : G.
Axiom derivative_of_cos : forall T : G, (d (cos T)) = (minus (times (sin T) (d T))).
Axiom derivative_of_sin : forall T : G, (d (sin T)) = (times (cos T) (d T)).
Axiom derivative_of_times : forall '+' T U : G, (d (times T U)) = ('+' (times T (d U)) (times U (d T))).
Axiom derivative_of_plus : forall '+' T U : G, (d ('+' T U)) = ('+' (d T) (d U)).
Axiom derivative_of_x : (d x) = one.
Axiom derivative_of_one : (d one) = zero.
Axiom derivative_of_zero : (d zero) = zero.
Axiom minus : forall '+' X : G, ('+' X (minus X)) = zero.
Axiom distributivity : forall '+' X Y Z : G, (times X ('+' Y Z)) = ('+' (times X Y) (times X Z)).
Axiom times_one : forall X : G, (times one X) = X.
Axiom times_zero : forall X : G, (times zero X) = zero.
Axiom plus_zero : forall '+' X : G, ('+' zero X) = X.
Axiom associativity_of_times : forall X Y Z : G, (times X (times Y Z)) = (times (times X Y) Z).
Axiom commutativity_of_times : forall X Y : G, (times X Y) = (times Y X).
Axiom associtivity_of_plus : forall '+' X Y Z : G, ('+' X ('+' Y Z)) = ('+' ('+' X Y) Z).
Axiom commutativity_of_plus : forall '+' X Y : G, ('+' X Y) = ('+' Y X).


(* Goal *)
Theorem check : forall T : G, (d T) = (times x (cos x)).
Proof.
  hammer.
Qed.

Check check.

