(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter commutator : G -> G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_associativity_of_commutator : forall A B C : G, (commutator (commutator A B) C) = (commutator A (commutator B C)).
Axiom ax_commutator : forall A B : G, (multiply A B) = (multiply B (multiply A (commutator A B))).
