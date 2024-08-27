(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a : hint_hack_compl.
Axiom ax_f06 : forall A B C : G, (mult (mult A B) (mult C C)) = (mult (mult A C) (mult B C)).
Axiom ax_f05 : forall A B C : G, (mult (mult A (mult A A)) (mult B C)) = (mult (mult A B) (mult (mult A A) C)).
Axiom ax_f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : G, (mult A (ld A B)) = B.

Complete ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 : a b c ld mult rd : hint
  for ((mult (mult a a) (mult b c)) = (mult (mult a b) (mult a c))).

(* Goal *)
Theorem check : (mult (mult a a) (mult b c)) = (mult (mult a b) (mult a c)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

