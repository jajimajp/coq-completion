Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

(* Set *)
Parameter G : Set.

Parameter s : G -> G.
Parameter p : G -> G.
Parameter plus : G -> G -> G.

(* Axioms *)
Axiom ax1 : forall x, s (p x) = x.
(* 左単位元 *)
Axiom ax2 : forall x, p (s x) = x.
(* 左逆元 *)
Axiom ax3 : forall x y, plus (s (x)) y = s (plus x y).

Create HintDb hint_compl.

Complete ax1 ax2 ax3 : plus s p : hint_compl.

Print Rewrite HintDb hint_compl.

Theorem check1 : forall x, s (p (s (p x))) = x.
  Proof.
    intros.
    autorewrite with hint_compl.
    reflexivity.
  Qed.

Check check1.
