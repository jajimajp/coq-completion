(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a2 : G.
Parameter b2 : G.
Parameter divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_inverse : forall A B : G, (inverse A) = (divide (divide B B) A).
Axiom ax_multiply : forall A B C : G, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom ax_single_axiom : forall A B C : G, (divide A (divide (divide (divide (divide B B) B) C) (divide (divide (divide B B) A) C))) = B.


(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  hammer.
Qed.

Check check.

