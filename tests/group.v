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
(* 結合律 *)
Axiom assoc : forall a b c, a + b + c = a + (b + c).
(* 左単位元 *)
Axiom id_l : forall a, e + a = a.
(* 左逆元 *)
Axiom inv_l : forall a, i a + a = e.

Create HintDb hint_compl.

Complete assoc id_l inv_l : f e i : hint_compl.

Theorem check1: forall x y, (i x) + (x + y) = y.
Proof.
  intros.
  autorewrite with hint_compl.
  reflexivity.
Qed.

Theorem check2: forall a b c, i (a + b) + (a + (b + c)) = c.
Proof.
  intros.
  autorewrite with hint_compl.
  reflexivity.
Qed.
