(*
This example was automatically generated by converting from
sp_com.trs: 

(VAR x y)
(RULES
+(x, y) -> +(y, x)
s(p(x)) -> x
p(s(x)) -> x
+(s(x), y) -> s(+(x, y))
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Parameter G : Set.
    
Parameter p : G -> G.
Parameter plus : G -> G -> G.
Parameter s : G -> G.
Axiom ax0 : forall x y, plus (s x) y = s (plus x y).
Axiom ax1 : forall x, p (s x) = x.
Axiom ax2 : forall x, s (p x) = x.
Axiom ax3 : forall x y, plus x y = plus y x.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 : p plus s : hint_compl.
Print Rewrite HintDb hint_compl.
