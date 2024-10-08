(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a : hint_hack_compl.
Axiom ax_group_axiom : forall W X Y Z : G, (multiply X (inverse (multiply (multiply (inverse (multiply (inverse Y) (multiply (inverse X) W))) Z) (inverse (multiply Y Z))))) = W.

Complete ax_group_axiom : a b c inverse multiply : hint
  for ((multiply a (multiply b c)) = (multiply (multiply a b) c)).

(* Goal *)
Theorem check : (multiply a (multiply b c)) = (multiply (multiply a b) c).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

