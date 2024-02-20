
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable and : G -> G -> G.
Variable not : G -> G.
Variable or : G -> G -> G.
Axiom ax0 : forall x y, not (and x y) = or (not (not (not x))) (not (not (not y))).
Axiom ax1 : forall x y, not (or x y) = and (not (not (not x))) (not (not (not y))).
Axiom ax2 : forall x, not (not x) = x.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 : and not or : hint_compl.
Print Rewrite HintDb hint_compl.
