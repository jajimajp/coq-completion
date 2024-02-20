
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable a : G.
Variable f : G -> G.
Axiom ax0 : a = f a.
Create HintDb hint_compl.
Complete ax0 : a f : hint_compl.
Print Rewrite HintDb hint_compl.
