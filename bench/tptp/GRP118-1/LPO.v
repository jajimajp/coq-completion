(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter identity : G.
Parameter multiply : G -> G -> G.
Axiom single_axiom : forall X Y Z : G, (multiply X (multiply (multiply X (multiply (multiply X Y) Z)) (multiply identity (multiply Z Z)))) = Y.

Complete single_axiom : identity multiply : hint
  for ((multiply (multiply a b) c) = (multiply a (multiply b c))).

(* Goal *)
Theorem check : (multiply (multiply a b) c) = (multiply a (multiply b c)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

