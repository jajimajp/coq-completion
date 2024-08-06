(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom identity : forall A : G, identity = (divide A A).
Axiom inverse : forall A : G, (inverse A) = (divide identity A).
Axiom multiply : forall A B : G, (multiply A B) = (divide A (divide identity B)).
Axiom single_axiom : forall A B C : G, (divide (divide identity (divide (divide (divide A B) C) A)) C) = B.


(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  hammer.
Qed.

Check check.

