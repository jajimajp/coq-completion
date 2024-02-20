
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable f : G -> G -> G.
Axiom ax0 : forall x y, f x y = f y x.
Create HintDb hint_compl.
Complete ax0 : f : hint_compl.
Print Rewrite HintDb hint_compl.
