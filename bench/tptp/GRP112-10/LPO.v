(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter a4 : G.
Parameter b1 : G.
Parameter b2 : G.
Parameter b3 : G.
Parameter b4 : G.
Parameter c3 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Parameter tuple : G -> G -> G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a1 : hint_hack_compl.
Axiom ax_single_axiom : forall X Y Z : G, (multiply (multiply (multiply X Y) Z) (multiply X Z)) = Y.

Complete ax_single_axiom : a1 a2 a3 a4 b1 b2 b3 b4 c3 inverse multiply tuple : hint
  for ((tuple (multiply (multiply (inverse b2) b2) a2) (multiply (multiply a3 b3) c3) (multiply (inverse a1) a1) (multiply a4 a4)) = (tuple a2 (multiply a3 (multiply b3 c3)) (multiply (inverse b1) b1) (multiply b4 b4))).

(* Goal *)
Theorem check : (tuple (multiply (multiply (inverse b2) b2) a2) (multiply (multiply a3 b3) c3) (multiply (inverse a1) a1) (multiply a4 a4)) = (tuple a2 (multiply a3 (multiply b3 c3)) (multiply (inverse b1) b1) (multiply b4 b4)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

