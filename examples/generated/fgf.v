
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable f : G -> G.
Variable g : G -> G.
Axiom ax0 : forall x, f (f x) = f (g (f x)).
Create HintDb hint_compl.
Complete ax0 : f g : hint_compl.
Print Rewrite HintDb hint_compl.
