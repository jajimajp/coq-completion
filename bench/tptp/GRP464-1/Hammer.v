(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom identity : forall A : G, identity = (divide A A).
Axiom inverse : forall A : G, (inverse A) = (divide identity A).
Axiom multiply : forall A B : G, (multiply A B) = (divide A (divide identity B)).
Axiom single_axiom : forall A B C : G, (divide A (divide (divide (divide (divide A A) B) C) (divide (divide identity A) C))) = B.


(* Goal *)
Theorem check : (multiply identity a2) = a2.
Proof.
  hammer.
Qed.

Check check.

