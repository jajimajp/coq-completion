(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom multiply : forall X Y : G, (multiply X Y) = (divide X (inverse Y)).
Axiom single_axiom : forall X Y Z : G, (divide (divide X (inverse (divide Y (divide X Z)))) Z) = Y.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.
