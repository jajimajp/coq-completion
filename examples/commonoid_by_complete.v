Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Parameter G : Set.
    
Parameter e : G.
Parameter f : G -> G -> G.
Axiom ax0 : forall x y, f x y = f y x.
Axiom ax1 : forall x, f e x = x.
Axiom ax2 : forall x y z, f (f x y) z = f x (f y z).

Theorem comm : forall x y, f x y = f y x.
  Proof.
    by_complete ax0 ax1 ax2 : e f.
  Qed.

Print comm.