(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter b1 : G.
Parameter divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a1.
Axiom ax_inverse : forall A B : G, (inverse A) = (divide (divide B B) A).
Axiom ax_multiply : forall A B C : G, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom ax_single_axiom : forall A B C : G, (divide A (divide B (divide C (divide A B)))) = C.

Complete ax_inverse ax_multiply ax_single_axiom : a1 b1 divide inverse multiply : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

