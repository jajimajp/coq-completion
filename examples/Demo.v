Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

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
(* (* 結合律 *) *)
(* Axiom assoc : forall a b c, a + b + c = a + (b + c). *)
(* (* 左単位元 *) *)
(* Axiom id_l : forall a, e + a = a. *)
(* (* 左逆元 *) *)
(* Axiom inv_l : forall a, i a + a = e. *)
Axiom ax : forall x y z, (x + y) + (y + z) = y.
Axiom ax2 : forall x y, (x + (x + x)) + y = x + y.

Create HintDb hint_compl.

Complete ax ax2 : : hint_compl for (forall x y z, x + ((x + y) + z) = (z + (x + y)) + y).
Print Rewrite HintDb hint_compl.

Theorem check1: forall x y z, x + ((x + y) + z) = (z + (x + y)) + y.
Proof.
  lpo_autorewrite with hint_compl.
  reflexivity.
Qed.

Print check1.
