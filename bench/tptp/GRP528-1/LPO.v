(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a.
Axiom ax_inverse : forall A B : G, (inverse A) = (divide (divide B B) A).
Axiom ax_multiply : forall A B C : G, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom ax_single_axiom : forall A B C : G, (divide A (divide (divide A B) (divide C B))) = C.

Complete ax_inverse ax_multiply ax_single_axiom : a b divide inverse multiply : hint
  for ((multiply a b) = (multiply b a)).

(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

