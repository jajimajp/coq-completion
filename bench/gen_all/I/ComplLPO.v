(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G -> G -> G.
Parameter k : G.
Parameter s : G.
Axiom k_definition : forall X Y : G, (a (a k X) Y) = X.
Axiom s_definition : forall X Y Z : G, (a (a (a s X) Y) Z) = (a (a X Z) (a Y Z)).

Complete k_definition s_definition : a k s : hint
  for ((a (a (a s k) k) x) = x).

(* Goal *)
Theorem check : (a (a (a s k) k) x) = x.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

