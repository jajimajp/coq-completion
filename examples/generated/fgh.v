
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable f : G -> G.
Variable g : G -> G.
Variable h : G -> G.
Axiom ax0 : forall x, f (h x) = h (h (f x)).
Axiom ax1 : forall x, f (g x) = g (f (f x)).
Create HintDb hint_compl.
Complete ax0 ax1 : f g h : hint_compl.
Print Rewrite HintDb hint_compl.
