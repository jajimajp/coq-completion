(*
This example was automatically generated by converting from
kamereon.trs: 

(VAR x y z)
(RULES
+(x, y) -> +(y, x)
+(+(x, y), z) -> +(x, +(y, z))
+(a, b) -> +(c, c)
+(b, c) -> +(a, a)
+(c, a) -> +(b, b)
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Parameter G : Set.
    
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter plus : G -> G -> G.
Axiom ax0 : plus c a = plus b b.
Axiom ax1 : plus b c = plus a a.
Axiom ax2 : plus a b = plus c c.
Axiom ax3 : forall x y z, plus (plus x y) z = plus x (plus y z).
Axiom ax4 : forall x y, plus x y = plus y x.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 : a b c plus : hint_compl.
Print Rewrite HintDb hint_compl.
