(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom multiply : forall A B : G, (multiply A B) = (divide A (inverse B)).
Axiom single_axiom : forall A B C : G, (divide (divide (divide A (inverse B)) C) (divide A C)) = B.


(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  hammer.
Qed.

Check check.

