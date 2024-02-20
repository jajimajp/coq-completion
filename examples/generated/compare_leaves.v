
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable concat : G -> G -> G.
Variable cons : G -> G -> G.
Variable false : G.
Variable leaf : G.
Variable less_leaves : G -> G -> G.
Variable true : G.
Axiom ax0 : forall u v w z, less_leaves (cons u v) (cons w z) = less_leaves (concat u v) (concat w z).
Axiom ax1 : forall w z, less_leaves leaf (cons w z) = true.
Axiom ax2 : forall x, less_leaves x leaf = false.
Axiom ax3 : forall u v y, concat (cons u v) y = cons u (concat v y).
Axiom ax4 : forall y, concat leaf y = y.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 : concat cons false leaf less_leaves true : hint_compl.
Print Rewrite HintDb hint_compl.
