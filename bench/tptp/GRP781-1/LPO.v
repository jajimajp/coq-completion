(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter c : G -> G -> G.
Parameter m : G -> G -> G.
Axiom assumption : forall X Y Z : G, (m X (m Y (m Z (m Y X)))) = (m Y (m X (m Z (m X Y)))).
Axiom commutator : forall X Y : G, (m Y (m X (c X Y))) = (m X Y).
