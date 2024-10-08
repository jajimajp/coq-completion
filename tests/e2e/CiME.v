Declare ML Module "coq-completion.plugin".

Require Import Coq.Setoids.Setoid.

Parameter G : Set.
    
Parameter append : G -> G -> G.
Parameter cons : G -> G -> G.
Parameter false : G.
Parameter hd : G -> G.
Parameter ifappend : G -> G -> G -> G.
Parameter is_empty : G -> G.
Parameter nil : G.
Parameter tl : G -> G.
Parameter true : G.
Axiom ax0 : forall l1 l2 x l, ifappend l1 l2 (cons x l) = cons x (append l l2).
Axiom ax1 : forall l1 l2, ifappend l1 l2 nil = l2.
Axiom ax2 : forall l1 l2, append l1 l2 = ifappend l1 l2 l1.
Axiom ax3 : forall x l, tl (cons x l) = l.
Axiom ax4 : forall x l, hd (cons x l) = x.
Axiom ax5 : forall x l, is_empty (cons x l) = false.
Axiom ax6 : is_empty nil = true.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 ax5 ax6 : append cons false hd ifappend is_empty nil tl true : hint_compl.
