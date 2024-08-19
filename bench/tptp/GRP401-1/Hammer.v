(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter commutator : G -> G -> G.
Parameter multiply : G -> G -> G.
Axiom commutator_distributes_over_product : forall A B C : G, (commutator (multiply A B) C) = (multiply (commutator A C) (commutator B C)).
Axiom commutator : forall A B : G, (multiply A B) = (multiply B (multiply A (commutator A B))).
