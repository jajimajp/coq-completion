(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter d : G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Hint Resolve a.
Axiom ax_c05 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_c03 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_c02 : forall A B : G, (mult A (ld A B)) = B.
Axiom ax_c01 : forall A B C : G, (mult A (mult B C)) = (mult (mult A B) (mult A C)).

Complete ax_c05 ax_c04 ax_c03 ax_c02 ax_c01 : a b c d ld mult rd : hint
  for ((mult (mult a b) (mult c d)) = (mult (mult a c) (mult b d))).

(* Goal *)
Theorem check : (mult (mult a b) (mult c d)) = (mult (mult a c) (mult b d)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

