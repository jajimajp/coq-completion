Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

(* 集合 *)
Variable G : Set.
(* + *)
Variable f : G -> G -> G.
Infix "+" := f (at level 50, left associativity).
(* 単位元 *)
Variable e : G.
(* - *)
Variable i : G -> G.

(**** 公理 ****)
(* 結合律 *)
Axiom assoc : forall a b c, a + b + c = a + (b + c).
(* 左単位元 *)
Axiom id_l : forall a, e + a = a.
(* 左逆元 *)
Axiom inv_l : forall a, i a + a = e.

Definition t0 := id_l.
Definition t1 := inv_l.
Definition t2 := assoc.

Create HintDb hint_compl.

Complete t0 t1 t2 : f e i : hint_compl.

Print Rewrite HintDb hint_compl.

Theorem check1: forall x y, (i x) + (x + y) = y.
Proof.
  intros.
  autorewrite with hint_compl.
  reflexivity.
Qed.

Print check1.

Theorem check2: forall a b c, i (a + b) + (a + (b + c)) = c.
Proof.
  intros.
  autorewrite with hint_compl.
  reflexivity.
Qed.

Print check2.
