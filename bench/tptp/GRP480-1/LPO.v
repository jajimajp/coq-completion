(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom multiply : forall A B : G, (multiply A B) = (divide A (inverse B)).
Axiom single_axiom : forall A B C D : G, (divide (inverse (divide (divide (divide A A) B) (divide C (divide B D)))) D) = C.

Complete multiply single_axiom : divide inverse multiply : hint
  for ((multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3))).

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

