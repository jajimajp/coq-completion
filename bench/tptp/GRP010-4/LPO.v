(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter b : G.
Parameter c : G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve b : hint_hack_compl.
Axiom ax_c_times_b_is_e : (multiply c b) = identity.
Axiom ax_left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).

Complete ax_c_times_b_is_e ax_left_inverse ax_left_identity ax_associativity : b c identity inverse multiply : hint
  for ((multiply b c) = identity).

(* Goal *)
Theorem check : (multiply b c) = identity.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

