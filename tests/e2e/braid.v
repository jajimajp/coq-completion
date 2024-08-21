Require Import Coq.Setoids.Setoid.
Require Import Loader.

(* 集合 *)
Parameter G : Set.

(* * *)
Parameter f : G -> G -> G.
Infix "*" := f (at level 40, left associativity).

(* 定数 *)
Parameter e : G.
Parameter c1 : G.
Parameter c2 : G.

(**** 公理 ****)
Axiom a0 : forall x : G, e * x = x.
Axiom a1 : forall x : G, x * e = x.
Axiom a2 : forall x y z : G, (x * y) * z = x * (y * z).
Axiom a3 : c1 * (c2 * c1) = c2 * (c1 * c2).
Axiom a4 : e = c1 * c1.
Axiom a5 : c2 * c2 = e.

Create HintDb hint_compl.

Complete a0 a1 a2 a3 a4 a5 : f e c1 c2 : hint_compl.

Theorem check1: c1 * c2 * c1 = c2 * c1 * c2.
Proof.
  lpo_autorewrite with hint_compl.
  reflexivity.
Qed.

