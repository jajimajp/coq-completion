(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter add : G -> G -> G.
Parameter p : G -> G.
Parameter s : G -> G.
Parameter z : G.
Axiom add_com : forall X Y : G, (add X Y) = (add Y X).
Axiom add_s : forall X Y : G, (add (s X) Y) = (s (add X Y)).
Axiom add_z : forall Y : G, (add z Y) = Y.
Axiom ps : forall X : G, (p (s X)) = X.
Axiom sp : forall X : G, (s (p X)) = X.

Complete add_com add_s add_z ps sp : add p s z : hint
  for ((add (s z) (p z)) = z).

(* Goal *)
Theorem check : (add (s z) (p z)) = z.
Proof.
  autorewrite with hint.
  reflexivity.
Qed.

Check check.
