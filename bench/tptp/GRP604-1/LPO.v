(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom multiply : forall A B : G, (multiply A B) = (inverse (double_divide B A)).
Axiom single_axiom : forall A B C : G, (inverse (double_divide (inverse (double_divide A (inverse (double_divide B (double_divide A C))))) C)) = B.

Complete multiply single_axiom :  : hint
  for ((multiply a b) = (multiply b a)).

(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

