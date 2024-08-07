(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom identity : forall X : G, identity = (divide X X).
Axiom inverse : forall X Z : G, (inverse X) = (divide (divide Z Z) X).
Axiom multiply : forall X Y Z : G, (multiply X Y) = (divide X (divide (divide Z Z) Y)).
Axiom single_axiom : forall X Y Z : G, (divide (divide X (divide (divide X Y) Z)) Y) = Z.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

