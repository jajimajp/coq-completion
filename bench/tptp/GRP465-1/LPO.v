(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a3 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_identity : forall A : G, identity = (divide A A).
Axiom ax_inverse : forall A : G, (inverse A) = (divide identity A).
Axiom ax_multiply : forall A B : G, (multiply A B) = (divide A (divide identity B)).
Axiom ax_single_axiom : forall A B C : G, (divide A (divide (divide (divide (divide A A) B) C) (divide (divide identity A) C))) = B.

Complete ax_identity ax_inverse ax_multiply ax_single_axiom : a3 b3 c3 divide identity inverse multiply : hint
  for ((multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3))).

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

