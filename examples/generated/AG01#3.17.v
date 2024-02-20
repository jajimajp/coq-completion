
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable app : G -> G -> G.
Variable cons : G -> G -> G.
Variable nil : G.
Variable plus : G -> G -> G.
Variable s : G -> G.
Variable sum : G -> G.
Variable zero : G.
Axiom ax0 : forall x y, plus (s x) y = s (plus x y).
Axiom ax1 : forall y, plus zero y = y.
Axiom ax2 : forall l x y k, sum (app l (cons x (cons y k))) = sum (app l (sum (cons x (cons y k)))).
Axiom ax3 : forall x y l, sum (cons x (cons y l)) = sum (cons (plus x y) l).
Axiom ax4 : forall x, sum (cons x nil) = cons x nil.
Axiom ax5 : forall x l k, app (cons x l) k = cons x (app l k).
Axiom ax6 : forall l, app l nil = l.
Axiom ax7 : forall k, app nil k = k.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 : app cons nil plus s sum zero : hint_compl.
Print Rewrite HintDb hint_compl.
