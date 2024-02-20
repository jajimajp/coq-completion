
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable d : G -> G -> G.
Variable m : G -> G -> G.
Variable s : G -> G.
Variable zero : G.
Axiom ax0 : forall x y, s (d (m x y) (s (s y))) = d (s (s x)) (s (s y)).
Axiom ax1 : forall x, s (d x (s zero)) = d (s x) (s zero).
Axiom ax2 : forall y, s (d zero (s y)) = d (s zero) (s y).
Axiom ax3 : forall x y, s (d (m x y) (s y)) = d (s x) (s y).
Axiom ax4 : forall y, d zero (s y) = zero.
Axiom ax5 : forall x y, m (s x) (s y) = m x y.
Axiom ax6 : forall y, m zero y = zero.
Axiom ax7 : forall x, m x zero = x.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 : d m s zero : hint_compl.
Print Rewrite HintDb hint_compl.
