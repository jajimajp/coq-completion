(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom multiply : forall X Y : G, (multiply X Y) = (inverse (double_divide Y X)).
Axiom single_axiom : forall X Y Z : G, (double_divide (inverse (double_divide X (inverse (double_divide (inverse Y) (double_divide X Z))))) Z) = Y.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

