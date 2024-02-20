
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable b : G.
Variable f : G -> G.
Axiom ax0 : forall y, f y = b.
Axiom ax1 : forall x y, f x = f y.
Create HintDb hint_compl.
Complete ax0 ax1 : b f : hint_compl.
Print Rewrite HintDb hint_compl.
