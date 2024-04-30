Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

(* 集合 *)
Parameter G : Set.
(* + *)
Parameter add : G -> G -> G.
Infix "+" := add (at level 50, left associativity).
(* * *)
Parameter mult : G -> G -> G.
Infix "*" := mult (at level 40, left associativity).

Parameter s : G -> G.
Parameter z : G.

(**** 公理 ****)
Axiom ax0 : forall a, z + a = a.
Axiom ax1 : forall a b, (s a) + b = s (a + b).
Axiom ax2 : forall a, z * a = z.
Axiom ax3 : forall a b, (s a) * b = (a * b) + b.

Create HintDb hint.

Complete ax0 ax1 ax2 ax3 : add mult s z : hint.

Print Rewrite HintDb hint.

Theorem mult_2_2_4: (s (s z)) * (s (s z)) = s (s (s (s z))).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Print mult_2_2_4.
