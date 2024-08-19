(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom inverse : forall A B : G, (inverse A) = (divide (divide B B) A).
Axiom multiply : forall A B C : G, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom single_axiom : forall A B C : G, (divide A (divide (divide (divide (divide B B) B) C) (divide (divide (divide B B) A) C))) = B.


(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  hammer.
Qed.

Check check.

