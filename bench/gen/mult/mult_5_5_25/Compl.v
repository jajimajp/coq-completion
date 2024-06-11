(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter add : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter s : G -> G.
Parameter z : G.
Axiom mult_s : forall X Y : G, (mult (s X) Y) = (add (mult X Y) Y).
Axiom mult_z : forall Y : G, (mult z Y) = z.
Axiom add_s : forall X Y : G, (add (s X) Y) = (s (add X Y)).
Axiom add_z : forall Y : G, (add z Y) = Y.

Complete mult_s mult_z add_s add_z : add mult s z : hint
  for ((mult (s (s (s (s (s z))))) (s (s (s (s (s z)))))) = (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z)))))))))))))))))))))))))).

(* Goal *)
Theorem check : (mult (s (s (s (s (s z))))) (s (s (s (s (s z)))))) = (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z))))))))))))))))))))))))).
Proof.
  autorewrite with hint.
  reflexivity.
Qed.

Check check.

