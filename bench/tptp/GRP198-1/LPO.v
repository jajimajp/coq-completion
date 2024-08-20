(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter multiply : G -> G -> G.
Axiom ax_condition : forall X Y : G, (multiply X (multiply Y (multiply Y (multiply Y (multiply X Y))))) = (multiply Y (multiply Y (multiply Y (multiply Y (multiply X X))))).
Axiom ax_left_cancellation : forall A B C : G, (multiply A B) = (multiply A C).
Axiom ax_right_cancellation : forall A B C : G, (multiply A B) = (multiply C B).
Axiom ax_associativity_of_multiply : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).

Complete ax_condition ax_left_cancellation ax_right_cancellation ax_associativity_of_multiply : a b multiply : hint
  for ((multiply b (multiply a (multiply b (multiply b (multiply b a))))) = (multiply a (multiply a (multiply b (multiply b (multiply b b)))))).

(* Goal *)
Theorem check : (multiply b (multiply a (multiply b (multiply b (multiply b a))))) = (multiply a (multiply a (multiply b (multiply b (multiply b b))))).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

