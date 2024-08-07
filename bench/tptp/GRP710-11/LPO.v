(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter i : G -> G.
Parameter mult : G -> G -> G.
Parameter unit : G.
Axiom f05 : forall A : G, (mult (i A) A) = unit.
Axiom f04 : forall A : G, (mult A (i A)) = unit.
Axiom f03 : forall A B C : G, (mult A (mult B (mult B C))) = (mult (mult (mult A B) B) C).
Axiom f02 : forall A : G, (mult unit A) = A.
Axiom f01 : forall A : G, (mult A unit) = A.

Complete f05 f04 f03 f02 f01 : i mult unit : hint
  for (forall X5 : G, (mult X5 x4) = x3).

(* Goal *)
Theorem check : forall X5 : G, (mult X5 x4) = x3.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

