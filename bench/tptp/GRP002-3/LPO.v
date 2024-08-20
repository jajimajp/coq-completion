(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter commutator : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_x_cubed_is_identity : forall X : G, (multiply X (multiply X X)) = identity.
Axiom ax_commutator : forall X Y : G, (commutator X Y) = (multiply X (multiply Y (multiply (inverse X) (inverse Y)))).
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.

Complete ax_x_cubed_is_identity ax_commutator ax_associativity ax_left_inverse ax_left_identity : a b commutator identity inverse multiply : hint
  for ((commutator (commutator a b) b) = identity).

(* Goal *)
Theorem check : (commutator (commutator a b) b) = identity.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

