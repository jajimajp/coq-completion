(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom inverse : forall A B : G, (inverse A) = (divide (divide B B) A).
Axiom multiply : forall A B C : G, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom single_axiom : forall A B C : G, (divide (divide A (divide B C)) (divide A B)) = C.


(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  hammer.
Qed.

Check check.

