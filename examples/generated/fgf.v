(*
This example was automatically generated by converting from
fgf.trs: 

(VAR x)
(RULES
f(f(x)) -> f(g(f(x)))
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Parameter G : Set.
    
Parameter f : G -> G.
Parameter g : G -> G.
Axiom ax0 : forall x, f (f x) = f (g (f x)).
Create HintDb hint_compl.
Complete ax0 : f g : hint_compl.
Print Rewrite HintDb hint_compl.
