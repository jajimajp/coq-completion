Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

(* 集合 *)
Parameter G : Set.
(* + *)
Parameter add : G -> G -> G.
Infix "+" := add (at level 50, left associativity).

Parameter s : G -> G.
Parameter z : G.

(**** 公理 ****)
Axiom ax0 : forall a, z + a = a.
Axiom ax1 : forall a b, (s a) + b = s (a + b).

Create HintDb hint.

Complete ax0 ax1 : add s z : hint.

Print Rewrite HintDb hint.

Theorem check1: ((s z) + z) + z = s z.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Print check1.
