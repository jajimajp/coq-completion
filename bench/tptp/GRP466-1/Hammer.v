(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom multiply : forall A B : G, (multiply A B) = (divide A (inverse B)).
Axiom single_axiom : forall A B C D : G, (divide (divide A A) (divide B (divide (divide C (divide D B)) (inverse D)))) = C.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.
