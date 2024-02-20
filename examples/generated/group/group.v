
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable minus : G -> G.
Variable plus : G -> G -> G.
Variable zero : G.
Axiom ax0 : forall x y z, plus (plus x y) z = plus x (plus y z).
Axiom ax1 : forall x, plus (minus x) x = zero.
Axiom ax2 : forall y, plus zero y = y.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 : minus plus zero : hint_compl.
Print Rewrite HintDb hint_compl.
