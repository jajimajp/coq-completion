
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable d : G -> G -> G.
Variable m : G -> G -> G.
Variable s : G -> G.
Variable zero : G.
Axiom ax0 : forall x y, d (s x) (s y) = s (d (m x y) (s y)).
Axiom ax1 : forall y, d zero (s y) = zero.
Axiom ax2 : forall x y, m (s x) (s y) = m x y.
Axiom ax3 : forall y, m zero y = zero.
Axiom ax4 : forall x, m x zero = x.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 : d m s zero : hint_compl.
Print Rewrite HintDb hint_compl.
