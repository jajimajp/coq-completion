(*
This example was automatically generated by converting from
Bor4.1.10.trs: 

(VAR )
(RULES
a -> b
f(b) -> g(a)
h(a) -> h(f(a))
)
(COMMENT
phd thesis by Cristina Borralleras
Example 4.1.10
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable a : G.
Variable b : G.
Variable f : G -> G.
Variable g : G -> G.
Variable h : G -> G.
Axiom ax0 : h a = h (f a).
Axiom ax1 : f b = g a.
Axiom ax2 : a = b.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 : a b f g h : hint_compl.
Print Rewrite HintDb hint_compl.