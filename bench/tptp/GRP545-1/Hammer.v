(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom identity : forall A : G, identity = (divide A A).
Axiom inverse : forall A : G, (inverse A) = (divide identity A).
Axiom multiply : forall A B : G, (multiply A B) = (divide A (divide identity B)).
Axiom single_axiom : forall A B C : G, (divide (divide identity (divide A B)) (divide (divide B C) A)) = C.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

