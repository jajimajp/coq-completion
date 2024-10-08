(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter identity : G.
Parameter multiply : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a : hint_hack_compl.
Axiom ax_a_times_b_is_c : (multiply a b) = c.
Axiom ax_squareness : forall X : G, (multiply X X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).

Complete ax_a_times_b_is_c ax_squareness ax_left_identity ax_associativity : a b c identity multiply : hint
  for ((multiply b a) = c).

(* Goal *)
Theorem check : (multiply b a) = c.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

