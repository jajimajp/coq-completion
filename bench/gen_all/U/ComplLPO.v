(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G -> G -> G.
Parameter i : G.
Parameter k : G.
Parameter s : G.
Axiom i_definition : forall X : G, (a i X) = X.
Axiom k_definition : forall X Y : G, (a (a k X) Y) = X.
Axiom s_definition : forall X Y Z : G, (a (a (a s X) Y) Z) = (a (a X Z) (a Y Z)).

Complete i_definition k_definition s_definition : a i k s : hint
  for ((a (a (a (a s (a k (a s i))) (a (a s i) i)) x) y) = (a y (a (a x x) y))).

(* Goal *)
Theorem check : (a (a (a (a s (a k (a s i))) (a (a s i) i)) x) y) = (a y (a (a x x) y)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

