(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter b1 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_single_axiom : forall A B C D : G, (multiply A (inverse (multiply B (multiply C (multiply (multiply (inverse C) (inverse (multiply D B))) A))))) = D.

Complete ax_single_axiom : a1 b1 inverse multiply : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

