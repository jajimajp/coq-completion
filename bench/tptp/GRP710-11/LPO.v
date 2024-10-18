(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter i : G -> G.
Parameter mult : G -> G -> G.
Parameter unit : G.
Parameter x3 : G.
Parameter x4 : G.
Hint Resolve unit.
Axiom ax_f05 : forall A : G, (mult (i A) A) = unit.
Axiom ax_f04 : forall A : G, (mult A (i A)) = unit.
Axiom ax_f03 : forall A B C : G, (mult A (mult B (mult B C))) = (mult (mult (mult A B) B) C).
Axiom ax_f02 : forall A : G, (mult unit A) = A.
Axiom ax_f01 : forall A : G, (mult A unit) = A.

Complete ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 : i mult unit x3 x4 : hint
  for (forall X5 : G, (mult X5 x4) = x3).

(* Goal *)
Theorem check : forall X5 : G, (mult X5 x4) = x3.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

