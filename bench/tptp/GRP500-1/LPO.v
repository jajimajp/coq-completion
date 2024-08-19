(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom multiply : forall A B : G, (multiply A B) = (inverse (double_divide B A)).
Axiom single_axiom : forall A B C D : G, (double_divide (inverse A) (inverse (double_divide (inverse (double_divide A (double_divide B C))) (double_divide D (double_divide B D))))) = C.

Complete multiply single_axiom :  : hint
  for ((multiply (multiply (inverse b2) b2) a2) = a2).

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

