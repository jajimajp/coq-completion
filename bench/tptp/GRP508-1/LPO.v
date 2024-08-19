(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom single_axiom : forall A B C D E F : G, (multiply (inverse (multiply (inverse (multiply (inverse (multiply A B)) (multiply B A))) (multiply (inverse (multiply C D)) (multiply C (inverse (multiply (multiply E (inverse F)) (inverse D))))))) F) = E.

Complete single_axiom :  : hint
  for ((multiply a b) = (multiply b a)).

(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

