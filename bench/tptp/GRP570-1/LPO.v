(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a2 : G.
Parameter double_divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a2.
Axiom ax_identity : forall A : G, identity = (double_divide A (inverse A)).
Axiom ax_inverse : forall A : G, (inverse A) = (double_divide A identity).
Axiom ax_multiply : forall A B : G, (multiply A B) = (double_divide (double_divide B A) identity).
Axiom ax_single_axiom : forall A B C : G, (double_divide (double_divide A (double_divide (double_divide B (double_divide A C)) (double_divide C identity))) (double_divide identity identity)) = B.

Complete ax_identity ax_inverse ax_multiply ax_single_axiom : a2 double_divide identity inverse multiply : hint
  for ((multiply identity a2) = a2).

(* Goal *)
Theorem check : (multiply identity a2) = a2.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

