(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter multiply : G -> G -> G.
Axiom condition : forall X Y : G, (multiply X (multiply Y (multiply Y (multiply Y (multiply X Y))))) = (multiply Y (multiply Y (multiply Y (multiply Y (multiply X X))))).
