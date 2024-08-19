(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom single_axiom : forall A B C : G, (inverse (multiply (inverse (multiply A (inverse (multiply (inverse B) (inverse (multiply C (inverse (multiply (inverse C) C)))))))) (multiply A C))) = B.

Complete single_axiom :  : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

