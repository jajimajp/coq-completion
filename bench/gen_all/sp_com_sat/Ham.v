(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter add : G -> G -> G.
Parameter p : G -> G.
Parameter s : G -> G.
Parameter z : G.
Axiom add_com : forall X Y : G, (add X Y) = (add Y X).
Axiom add_s : forall X Y : G, (add (s X) Y) = (s (add X Y)).
Axiom add_z : forall Y : G, (add z Y) = Y.
Axiom ps : forall X : G, (p (s X)) = X.
Axiom sp : forall X : G, (s (p X)) = X.


(* Goal *)
Theorem check : (add (s z) (p z)) = (s z).
Proof.
  hammer.
Qed.

Check check.

