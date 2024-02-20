
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable cons : G -> G -> G.
Variable last : G -> G -> G.
Variable nil : G.
Variable rev : G -> G.
Axiom ax0 : forall x y l, last x (cons y l) = last y l.
Axiom ax1 : forall x, last x nil = x.
Axiom ax2 : forall x l, rev (cons x l) = cons (last x l) (rev l).
Axiom ax3 : rev nil = nil.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 : cons last nil rev : hint_compl.
Print Rewrite HintDb hint_compl.
