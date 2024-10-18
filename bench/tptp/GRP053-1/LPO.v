(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter b1 : G.
Parameter b2 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a1.
Axiom ax_single_axiom : forall X Y Z : G, (inverse (multiply Y (inverse (multiply (inverse (multiply (inverse (multiply Z Y)) (multiply Z (inverse X)))) (inverse (multiply (inverse Y) Y)))))) = X.

Complete ax_single_axiom : a1 a2 a3 b1 b2 b3 c3 inverse multiply : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

