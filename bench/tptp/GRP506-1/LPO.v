(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a2 : G.
Parameter b2 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a2 : hint_hack_compl.
Axiom ax_single_axiom : forall A B C D E F : G, (multiply (inverse (multiply (inverse (multiply (inverse (multiply A B)) (multiply B A))) (multiply (inverse (multiply C D)) (multiply C (inverse (multiply (multiply E (inverse F)) (inverse D))))))) F) = E.

Complete ax_single_axiom : a2 b2 inverse multiply : hint
  for ((multiply (multiply (inverse b2) b2) a2) = a2).

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

