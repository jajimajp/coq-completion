
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable a : G -> G -> G.
Variable cur : G -> G.
Variable i : G.
Variable one : G.
Variable p : G -> G -> G.
Variable up : G.
Axiom ax0 : forall x y, a up (p x y) = y.
Axiom ax1 : forall x y, a one (p x y) = x.
Axiom ax2 : a up i = up.
Axiom ax3 : a one i = one.
Axiom ax4 : forall x, a i x = x.
Axiom ax5 : forall x y z, a (a x y) z = a x (a y z).
Axiom ax6 : forall x y z, a (p x y) z = p (a x z) (a y z).
Axiom ax7 : forall x y, a (cur x) y = cur (a x (p one (a y up))).
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 : a cur i one p up : hint_compl.
Print Rewrite HintDb hint_compl.
