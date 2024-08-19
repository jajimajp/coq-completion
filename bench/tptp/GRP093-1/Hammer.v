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
Axiom inverse : forall X : G, (inverse X) = (divide identity X).
Axiom multiply : forall X Y : G, (multiply X Y) = (divide X (divide identity Y)).
Axiom single_axiom : forall X Y Z : G, (divide (divide identity (divide (divide (divide X Y) Z) X)) Z) = Y.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

