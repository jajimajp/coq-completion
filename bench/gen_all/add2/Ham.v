(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter add : G -> G -> G.
Parameter s : G -> G.
Parameter z : G.
Axiom add_s : forall X Y : G, (add (s X) Y) = (s (add X Y)).
Axiom add_z : forall Y : G, (add z Y) = Y.


(* Goal *)
Theorem check : (add (s (add z z)) z) = (s z).
Proof.
  hammer.
Qed.

Check check.
