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
Parameter unit : G.
Hint Resolve a.
Axiom ax_c07 : forall A B C : G, (ld A (mult (mult A B) C)) = (rd (mult B (mult C A)) A).
Axiom ax_c06 : forall A : G, (mult unit A) = A.
Axiom ax_c05 : forall A : G, (mult A unit) = A.
Axiom ax_c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_c01 : forall A B : G, (mult A (ld A B)) = B.

Complete ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01 : a b c ld mult rd unit : hint
  for ((mult a (mult (mult b (mult b (mult b b))) c)) = (mult (mult a (mult b (mult b (mult b b)))) c)).

(* Goal *)
Theorem check : (mult a (mult (mult b (mult b (mult b b))) c)) = (mult (mult a (mult b (mult b (mult b b)))) c).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

