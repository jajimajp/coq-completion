(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom multiply : forall X Y : G, (multiply X Y) = (inverse (double_divide Y X)).
Axiom single_axiom : forall U X Y Z : G, (inverse (double_divide (double_divide X (double_divide (double_divide Y Z) (inverse (double_divide Y (double_divide (inverse U) (inverse Z)))))) X)) = U.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

