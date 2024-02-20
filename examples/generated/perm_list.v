
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable add : G -> G -> G.
Variable app : G -> G -> G.
Variable nil : G.
Variable reverse : G -> G.
Variable shuffle : G -> G.
Axiom ax0 : forall n x, shuffle (add n x) = add n (shuffle (reverse x)).
Axiom ax1 : shuffle nil = nil.
Axiom ax2 : forall n x, reverse (add n x) = app (reverse x) (add n nil).
Axiom ax3 : reverse nil = nil.
Axiom ax4 : forall n x y, app (add n x) y = add n (app x y).
Axiom ax5 : forall y, app nil y = y.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 ax5 : add app nil reverse shuffle : hint_compl.
Print Rewrite HintDb hint_compl.
