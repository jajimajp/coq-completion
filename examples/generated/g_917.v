
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable a : G.
Variable b : G.
Variable c : G.
Variable f : G -> G -> G.
Axiom ax0 : b = a.
Axiom ax1 : a = b.
Axiom ax2 : forall x, f x x = c.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 : a b c f : hint_compl.
Print Rewrite HintDb hint_compl.
