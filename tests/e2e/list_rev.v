Declare ML Module "coq-completion.plugin".

Require Import Coq.Setoids.Setoid.

Parameter G : Set.
    
Parameter cons : G -> G -> G.
Parameter last : G -> G -> G.
Parameter nil : G.
Parameter rev : G -> G.
Axiom ax0 : forall x y l, last x (cons y l) = last y l.
Axiom ax1 : forall x, last x nil = x.
Axiom ax2 : forall x l, rev (cons x l) = cons (last x l) (rev l).
Axiom ax3 : rev nil = nil.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 : cons last nil rev : hint_compl.
