Require Import Coq.Setoids.Setoid.
Require Import Loader.

(* 集合 *)
Variable G : Set.

(* * *)
Variable f : G -> G -> G.
Infix "*" := f (at level 40, left associativity).

(* 定数 *)
Variable e : G.
Variable c1 : G.
Variable c2 : G.

(**** 公理 ****)
Axiom t0 : forall x : G, e * x = x.
Axiom t1 : forall x : G, x * e = x.
Axiom t2 : forall x y z : G, (x * y) * z = x * (y * z).
Axiom t3 : c1 * (c2 * c1) = c2 * (c1 * c2).
Axiom t4 : e = c1 * c1.
Axiom t5 : c2 * c2 = e.

Create HintDb hint_compl.

Complete t0 t1 t2 t3 t4 t5 : f e c1 c2 : hint_compl.

Print Rewrite HintDb hint_compl.

Theorem check1: c1 * c2 * c1 = c2 * c1 * c2.
Proof.
  intros.
  autorewrite with hint_compl.
  reflexivity.
Qed.

Print check1.
