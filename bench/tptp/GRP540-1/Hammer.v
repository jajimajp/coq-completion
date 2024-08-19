(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom identity : forall A : G, identity = (divide A A).
Axiom inverse : forall A B : G, (inverse A) = (divide (divide B B) A).
Axiom multiply : forall A B C : G, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom single_axiom : forall A B C : G, (divide (divide A B) (divide (divide A C) B)) = C.


(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  hammer.
Qed.

Check check.

