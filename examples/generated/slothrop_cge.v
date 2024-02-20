
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable f : G -> G.
Variable g : G -> G.
Variable refl : G.
Variable symm : G -> G.
Variable trans : G -> G -> G.
Axiom ax0 : forall x y, trans (f x) (g y) = trans (g y) (f x).
Axiom ax1 : forall x y, trans (g x) (g y) = g (trans x y).
Axiom ax2 : forall x y, trans (f x) (f y) = f (trans x y).
Axiom ax3 : forall x, trans refl x = x.
Axiom ax4 : forall x, trans (symm x) x = refl.
Axiom ax5 : forall x y z, trans (trans x y) z = trans x (trans y z).
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 ax5 : f g refl symm trans : hint_compl.
Print Rewrite HintDb hint_compl.
