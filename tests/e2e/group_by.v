Declare ML Module "coq-completion.plugin".

Require Import Coq.Setoids.Setoid.

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


Create HintDb hint.
Complete assoc id_l inv_l : f e i : hint for (forall x y, (i x) + (x + y) = y).
Theorem check1: forall x y, (i x) + (x + y) = y.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Create HintDb hint2.
Complete assoc id_l inv_l : f e i : hint2 for (forall x y, (i x) + (x + y) = y).
Theorem check2: forall x y, (i x) + (x + y) = y.
Proof.
  lpo_autorewrite with hint2.
  reflexivity.
Qed.