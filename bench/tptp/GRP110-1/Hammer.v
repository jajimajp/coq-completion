(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter a4 : G.
Parameter b1 : G.
Parameter b2 : G.
Parameter b3 : G.
Parameter b4 : G.
Parameter c3 : G.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_multiply : forall X Y : G, (multiply X Y) = (inverse (double_divide Y X)).
Axiom ax_single_axiom : forall X Y Z : G, (inverse (double_divide (inverse (double_divide (inverse (double_divide X Y)) Z)) (double_divide X Z))) = Y.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

