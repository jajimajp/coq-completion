(*
This example was automatically generated by converting from
devie_ex8.12.trs: 

(VAR x)
(RULES
f1(g1(i1(x))) -> g1(i1(f1(g1(i2(x)))))
f2(g2(i2(x))) -> g2(i2(f2(g2(i1(x)))))
g1(a) -> a
g2(a) -> a
h1(g1(i1(x))) -> g1(i1(x))
h2(g2(i2(x))) -> g2(i2(x))
h1(a) -> a
h2(a) -> a
f1(a) -> a
f2(a) -> a
i1(a) -> a
i2(a) -> a
)
(COMMENT
According to Devie 1991,
No ground total reduction order can complete this system.
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable a : G.
Variable f1 : G -> G.
Variable f2 : G -> G.
Variable g1 : G -> G.
Variable g2 : G -> G.
Variable h1 : G -> G.
Variable h2 : G -> G.
Variable i1 : G -> G.
Variable i2 : G -> G.
Axiom ax0 : i2 a = a.
Axiom ax1 : i1 a = a.
Axiom ax2 : f2 a = a.
Axiom ax3 : f1 a = a.
Axiom ax4 : h2 a = a.
Axiom ax5 : h1 a = a.
Axiom ax6 : forall x, h2 (g2 (i2 x)) = g2 (i2 x).
Axiom ax7 : forall x, h1 (g1 (i1 x)) = g1 (i1 x).
Axiom ax8 : g2 a = a.
Axiom ax9 : g1 a = a.
Axiom ax10 : forall x, f2 (g2 (i2 x)) = g2 (i2 (f2 (g2 (i1 x)))).
Axiom ax11 : forall x, f1 (g1 (i1 x)) = g1 (i1 (f1 (g1 (i2 x)))).
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8 ax9 ax10 ax11 : a f1 f2 g1 g2 h1 h2 i1 i2 : hint_compl.
Print Rewrite HintDb hint_compl.
