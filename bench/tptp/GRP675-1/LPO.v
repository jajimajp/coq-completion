(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter asoc : G -> G -> G -> G.
Parameter b : G.
Parameter c : G.
Parameter d : G.
Parameter e : G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
(* HACK: for coq-completion *)
Hint Resolve a : hint_hack_compl.
Axiom ax_c09 : forall A B C : G, (asoc A B C) = (ld (mult A (mult B C)) (mult (mult A B) C)).
Axiom ax_c08 : forall A B C : G, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom ax_c07 : forall A B C : G, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom ax_c06 : forall A : G, (mult unit A) = A.
Axiom ax_c05 : forall A : G, (mult A unit) = A.
Axiom ax_c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_c01 : forall A B : G, (mult A (ld A B)) = B.

Complete ax_c09 ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01 : a asoc b c d e ld mult rd unit : hint
  for ((mult (asoc a b c) (mult d e)) = (mult (mult (asoc a b c) d) e)).

(* Goal *)
Theorem check : (mult (asoc a b c) (mult d e)) = (mult (mult (asoc a b c) d) e).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

