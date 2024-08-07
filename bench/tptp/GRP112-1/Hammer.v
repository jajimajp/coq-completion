(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter multiply : G -> G -> G.
Axiom single_axiom : forall X Y Z : G, (multiply (multiply (multiply X Y) Z) (multiply X Z)) = Y.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

