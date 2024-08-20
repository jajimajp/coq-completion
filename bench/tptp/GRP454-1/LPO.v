(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_identity : forall A : G, identity = (divide A A).
Axiom ax_inverse : forall A : G, (inverse A) = (divide identity A).
Axiom ax_multiply : forall A B : G, (multiply A B) = (divide A (divide identity B)).
Axiom ax_single_axiom : forall A B C : G, (divide (divide identity (divide A (divide B (divide (divide (divide A A) A) C)))) C) = B.

Complete ax_identity ax_inverse ax_multiply ax_single_axiom : a1 divide identity inverse multiply : hint
  for ((multiply (inverse a1) a1) = identity).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

