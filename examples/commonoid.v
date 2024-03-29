(*
This example was automatically generated by converting from
commonoid.trs: 

(VAR x y z)
(RULES
f(f(x,y),z) -> f(x,f(y,z))
f(e,x) -> x
f(x,y) -> f(y,x)
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Variable G : Set.
    
Variable e : G.
Variable f : G -> G -> G.
Axiom ax0 : forall x y, f x y = f y x.
Axiom ax1 : forall x, f e x = x.
Axiom ax2 : forall x y z, f (f x y) z = f x (f y z).
Create HintDb hint_compl.
Complete ax0 ax1 ax2 : e f : hint_compl.
Print Rewrite HintDb hint_compl.

Theorem comm : forall x y, f x y = f y x.
  Proof.
    intros.
    lpo_autorewrite with hint_compl.
    reflexivity.
  Qed.

Print comm.