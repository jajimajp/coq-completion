
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable evenodd : G -> G -> G.
Variable false : G.
Variable not : G -> G.
Variable s : G -> G.
Variable true : G.
Variable zero : G.
Axiom ax0 : forall x, evenodd (s x) (s zero) = evenodd x zero.
Axiom ax1 : evenodd zero (s zero) = false.
Axiom ax2 : forall x, evenodd x zero = not (evenodd x (s zero)).
Axiom ax3 : not false = true.
Axiom ax4 : not true = false.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 : evenodd false not s true zero : hint_compl.
Print Rewrite HintDb hint_compl.
