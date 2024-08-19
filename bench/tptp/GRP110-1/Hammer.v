(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom multiply : forall X Y : G, (multiply X Y) = (inverse (double_divide Y X)).
Axiom single_axiom : forall X Y Z : G, (inverse (double_divide (inverse (double_divide (inverse (double_divide X Y)) Z)) (double_divide X Z))) = Y.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

