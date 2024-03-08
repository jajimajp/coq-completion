(*
This example was automatically generated by converting from
sp.trs: 

(VAR x y)
(RULES
s(p(x)) -> x
p(s(x)) -> x
+(s(x), y) -> s(+(x, y))
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable p : G -> G.
Variable plus : G -> G -> G.
Variable s : G -> G.
Axiom ax0 : forall x y, plus (s x) y = s (plus x y).
Axiom ax1 : forall x, p (s x) = x.
Axiom ax2 : forall x, s (p x) = x.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 : p plus s : hint_compl.
Print Rewrite HintDb hint_compl.