
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable a : G -> G -> G.
Variable s : G -> G.
Variable zero : G.
Axiom ax0 : forall x y, a (s x) (s y) = a x (a (s x) y).
Axiom ax1 : forall x, a (s x) zero = a x (s zero).
Axiom ax2 : forall y, a zero y = s y.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 : a s zero : hint_compl.
Print Rewrite HintDb hint_compl.
