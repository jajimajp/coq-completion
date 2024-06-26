(*
This example was automatically generated by converting from
group.trs: 

(VAR x y z)
(RULES
+(0, y) -> y
+(-(x), x) -> 0
+(+(x, y), z) -> +(x, +(y, z))
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Parameter G : Set.
    
Parameter minus : G -> G.
Parameter plus : G -> G -> G.
Parameter zero : G.
Axiom ax0 : forall x y z, plus (plus x y) z = plus x (plus y z).
Axiom ax1 : forall x, plus (minus x) x = zero.
Axiom ax2 : forall y, plus zero y = y.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 : minus plus zero : hint_compl.
Print Rewrite HintDb hint_compl.
