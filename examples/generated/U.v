
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable a : G -> G -> G.
Variable i : G.
Variable k : G.
Variable s : G.
Variable x : G.
Variable y : G.
Axiom ax0 : a (a (a s i) (a x x)) y = a (a i y) (a (a x x) y).
Axiom ax1 : a (a (a s i) i) x = a (a i x) (a i x).
Axiom ax2 : a (a (a s (a k (a s i))) (a (a s i) i)) x = a (a (a k (a s i)) x) (a (a (a s i) i) x).
Axiom ax3 : forall X, a i X = X.
Axiom ax4 : forall X Y, a (a k X) Y = X.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 : a i k s x y : hint_compl.
Print Rewrite HintDb hint_compl.
