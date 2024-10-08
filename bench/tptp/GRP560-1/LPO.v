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
(* HACK: for coq-completion *)
Hint Resolve a : hint_hack_compl.
Axiom ax_multiply : forall A B : G, (multiply A B) = (divide A (inverse B)).
Axiom ax_single_axiom : forall A B C : G, (divide A (inverse (divide (divide B C) (divide A C)))) = B.

Complete ax_multiply ax_single_axiom : a b divide inverse multiply : hint
  for ((multiply a b) = (multiply b a)).

(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

