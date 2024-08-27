(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter double_divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a1 : hint_hack_compl.
Axiom ax_identity : forall A : G, identity = (double_divide A (inverse A)).
Axiom ax_inverse : forall A : G, (inverse A) = (double_divide A identity).
Axiom ax_multiply : forall A B : G, (multiply A B) = (double_divide (double_divide B A) identity).
Axiom ax_single_axiom : forall A B C D : G, (double_divide (double_divide (double_divide A (double_divide B identity)) (double_divide (double_divide C (double_divide D (double_divide D identity))) (double_divide A identity))) B) = C.

Complete ax_identity ax_inverse ax_multiply ax_single_axiom : a1 double_divide identity inverse multiply : hint
  for ((multiply (inverse a1) a1) = identity).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

