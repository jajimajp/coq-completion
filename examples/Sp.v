Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

(* Set *)
Variable G : Set.

Variable s : G -> G.
Variable p : G -> G.
Variable plus : G -> G -> G.

(* Axioms *)
Axiom ax1 : forall x, s (p x) = x.
(* 左単位元 *)
Axiom ax2 : forall x, p (s x) = x.
(* 左逆元 *)
Axiom ax3 : forall x y, plus (s (x)) y = s (plus x y).

Create HintDb hint_compl.

Definition t0 := ax1.
Definition t1 := ax2.
Definition t2 := ax3.


Complete ax1 ax2 ax3 : plus s p : hint_compl.

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
