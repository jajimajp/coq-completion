(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter commutator : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom associativity_of_commutator : forall X Y Z : G, (commutator (commutator X Y) Z) = (commutator X (commutator Y Z)).
Axiom name : forall X Y : G, (commutator X Y) = (multiply (inverse X) (multiply (inverse Y) (multiply X Y))).
Axiom associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : G, (multiply identity X) = X.

Complete associativity_of_commutator name associativity left_inverse left_identity : commutator identity inverse multiply : hint
  for ((multiply a (commutator b c)) = (multiply (commutator b c) a)).

(* Goal *)
Theorem check : (multiply a (commutator b c)) = (multiply (commutator b c) a).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

