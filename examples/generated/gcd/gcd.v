
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable false : G.
Variable gcd : G -> G -> G.
Variable if_gcd : G -> G -> G -> G.
Variable le : G -> G -> G.
Variable minus : G -> G -> G.
Variable s : G -> G.
Variable true : G.
Variable z : G.
Axiom ax0 : forall X Y, if_gcd false (s X) (s Y) = gcd (minus Y X) (s X).
Axiom ax1 : forall X Y, if_gcd true (s X) (s Y) = gcd (minus X Y) (s Y).
Axiom ax2 : forall X Y, gcd (s X) (s Y) = if_gcd (le Y X) (s X) (s Y).
Axiom ax3 : forall X, gcd (s X) z = s X.
Axiom ax4 : forall Y, gcd z Y = Y.
Axiom ax5 : forall X Y, minus (s X) (s Y) = minus X Y.
Axiom ax6 : forall X, minus X z = X.
Axiom ax7 : forall X Y, le (s X) (s X) = le X Y.
Axiom ax8 : forall X, le (s X) z = false.
Axiom ax9 : forall Y, le z Y = true.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8 ax9 : false gcd if_gcd le minus s true z : hint_compl.
Print Rewrite HintDb hint_compl.
