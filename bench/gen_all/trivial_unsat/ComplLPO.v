(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.

Complete  :  : hint
  for (forall X Y : G, (f X) = (f Y)).

(* Goal *)
Theorem check : forall X Y : G, (f X) = (f Y).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.
