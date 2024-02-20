WARNING: multiple VAR lines found in .trs file. This may cause unexpected behavior.

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable a | x == a : G.
Variable b | x == b : G.
Variable f : G -> G.
Axiom ax0 : forall x, f x = b | x == b.
Axiom ax1 : forall x, f x = a | x == a.
Create HintDb hint_compl.
Complete ax0 ax1 : a | x == a b | x == b f : hint_compl.
Print Rewrite HintDb hint_compl.
