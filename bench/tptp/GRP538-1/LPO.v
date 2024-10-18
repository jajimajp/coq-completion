(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a2 : G.
Parameter b2 : G.
Parameter divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a2.
Axiom ax_identity : forall A : G, identity = (divide A A).
Axiom ax_inverse : forall A B : G, (inverse A) = (divide (divide B B) A).
Axiom ax_multiply : forall A B C : G, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom ax_single_axiom : forall A B C : G, (divide (divide A B) (divide (divide A C) B)) = C.

Complete ax_identity ax_inverse ax_multiply ax_single_axiom : a2 b2 divide identity inverse multiply : hint
  for ((multiply (multiply (inverse b2) b2) a2) = a2).

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

