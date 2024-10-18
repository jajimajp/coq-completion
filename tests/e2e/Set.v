Declare ML Module "coq-completion.plugin".
Require Import Coq.Setoids.Setoid.

Parameter S : Set.
(* + *)
Parameter f : S -> S -> S.
Infix "+" := f (at level 50, left associativity).
(* 単位元 *)
Parameter e : S.
(* - *)
Parameter i : S -> S.

(**** 公理 ****)
(* 結合律 *)
Axiom assoc : forall a b c, a + b + c = a + (b + c).
(* 左単位元 *)
Axiom id_l : forall a, e + a = a.
(* 左逆元 *)
Axiom inv_l : forall a, i a + a = e.


Complete assoc id_l inv_l : f e i : hint.

Theorem check1: forall x y, (i x) + (x + y) = y.
Proof.
  intros.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check1.
