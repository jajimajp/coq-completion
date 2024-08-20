(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter identity : G.
Parameter multiply : G -> G -> G.
Axiom ax_single_axiom2 : (multiply identity identity) = identity.
Axiom ax_single_axiom : forall X Y Z : G, (multiply Y (multiply (multiply Y (multiply (multiply Y Y) (multiply X Z))) (multiply Z (multiply Z Z)))) = X.

Complete ax_single_axiom2 ax_single_axiom : a identity multiply : hint
  for ((multiply identity a) = a).

(* Goal *)
Theorem check : (multiply identity a) = a.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

