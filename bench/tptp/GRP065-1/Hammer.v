(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter b1 : G.
Parameter b2 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_inverse : forall X Z : G, (inverse X) = (divide (divide Z Z) X).
Axiom ax_multiply : forall X Y Z : G, (multiply X Y) = (divide X (divide (divide Z Z) Y)).
Axiom ax_single_axiom : forall X Y Z : G, (divide (divide (divide X X) (divide X (divide Y (divide (divide (divide X X) X) Z)))) Z) = Y.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

