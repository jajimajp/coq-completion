(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom multiply : forall A B : G, (multiply A B) = (inverse (double_divide B A)).
Axiom single_axiom : forall A B C : G, (double_divide A (inverse (double_divide (inverse (double_divide (double_divide A B) (inverse C))) B))) = C.

Complete multiply single_axiom : double_divide inverse multiply : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

