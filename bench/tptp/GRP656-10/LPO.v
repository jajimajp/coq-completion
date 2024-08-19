(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Axiom f05 : forall A B C : G, (mult (mult A B) (mult C A)) = (mult (mult A (mult B C)) A).
Axiom f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom f01 : forall A B : G, (mult A (ld A B)) = B.

Complete f05 f04 f03 f02 f01 : ld mult rd : hint
  for (forall X0 : G, (tuple (mult X0 (x1 X0)) (mult (x1_2 X0) X0)) = (tuple (x1 X0) (x1_2 X0))).

(* Goal *)
Theorem check : forall X0 : G, (tuple (mult X0 (x1 X0)) (mult (x1_2 X0) X0)) = (tuple (x1 X0) (x1_2 X0)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

