
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable @ : G -> G -> G.
Variable add : G.
Variable double : G.
Variable s : G.
Variable zero : G.
Axiom ax0 : forall x, @ double x = @ (@ add x) x.
Axiom ax1 : forall x y, @ (@ add (@ s x)) y = @ s (@ (@ add x) y).
Axiom ax2 : forall y, @ (@ add zero) y = y.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 : @ add double s zero : hint_compl.
Print Rewrite HintDb hint_compl.
