(*
This example was automatically generated by converting from
simply-but-non-totally-terminating.trs: 

(VAR x)
(RULES
f(g(h(x))) -> f(h(h(g(g(x)))))
)
(COMMENT
Zantema 1994 Ch 2.4
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Parameter G : Set.
    
Parameter f : G -> G.
Parameter g : G -> G.
Parameter h : G -> G.
Axiom ax0 : forall x, f (g (h x)) = f (h (h (g (g x)))).
Create HintDb hint_compl.
Complete ax0 : f g h : hint_compl.
Print Rewrite HintDb hint_compl.
