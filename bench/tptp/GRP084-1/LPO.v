(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom single_axiom : forall U V W X Y Z : G, (multiply (inverse (multiply (inverse (multiply (inverse (multiply X Y)) (multiply Y X))) (multiply (inverse (multiply Z U)) (multiply Z (inverse (multiply (multiply V (inverse W)) (inverse U))))))) W) = V.

Complete single_axiom : inverse multiply : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.
