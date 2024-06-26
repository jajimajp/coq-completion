(*
This example was automatically generated by converting from
non-terminating.trs: 

(VAR )
(RULES
a -> f(a)
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Parameter G : Set.
    
Parameter a : G.
Parameter f : G -> G.
Axiom ax0 : a = f a.
Create HintDb hint_compl.
Complete ax0 : a f : hint_compl.
Print Rewrite HintDb hint_compl.
