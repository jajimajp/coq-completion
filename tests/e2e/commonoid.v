Require Import Coq.Setoids.Setoid.
Require Import Loader.

(* 集合 *)
Parameter G : Set.
(* + *)
Parameter f : G -> G -> G.
Infix "+" := f (at level 50, left associativity).
(* 単位元 *)
Parameter e : G.
(* - *)
Parameter i : G -> G.

(**** 公理 ****)
Axiom ax0 : forall x y, x + y = y + x.
Axiom ax1 : forall x, e + x = x.
Axiom ax2 : forall x y z, (x + y) + z = x + (y + z).

Create HintDb hint_compl.

Complete ax0 ax1 ax2 : f e i : hint_compl.

Theorem check: forall x y z, x + (y + z) = z + (x + y).
Proof.
  intros.
  lpo_autorewrite with hint_compl.
  reflexivity.
Qed.
