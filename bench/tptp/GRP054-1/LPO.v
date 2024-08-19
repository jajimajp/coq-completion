(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom single_axiom : forall X Y Z : G, (inverse (multiply (inverse (multiply Z (inverse (multiply (inverse X) (inverse (multiply Y (inverse (multiply (inverse Y) Y)))))))) (multiply Z Y))) = X.

Complete single_axiom :  : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

