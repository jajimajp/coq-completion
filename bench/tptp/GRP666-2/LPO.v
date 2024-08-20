(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter i : G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom ax_c11 : forall A B : G, (mult (mult A B) (i B)) = A.
Axiom ax_c10 : forall A B : G, (mult (i A) (mult A B)) = B.
Axiom ax_c09 : forall A B C : G, (ld A (mult (mult B C) A)) = (mult (ld A (mult B A)) (ld A (mult C A))).
Axiom ax_c08 : forall A B C D : G, (rd (mult (mult (mult A B) C) D) (mult C D)) = (mult (rd (mult (mult A C) D) (mult C D)) (rd (mult (mult B C) D) (mult C D))).
Axiom ax_c07 : forall A B C D : G, (ld (mult A B) (mult A (mult B (mult C D)))) = (mult (ld (mult A B) (mult A (mult B C))) (ld (mult A B) (mult A (mult B D)))).
Axiom ax_c06 : forall A : G, (mult unit A) = A.
Axiom ax_c05 : forall A : G, (mult A unit) = A.
Axiom ax_c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_c01 : forall A B : G, (mult A (ld A B)) = B.

Complete ax_c11 ax_c10 ax_c09 ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01 : a b c i ld mult rd unit : hint
  for ((mult a (mult b (mult a c))) = (mult (mult (mult a b) a) c)).

(* Goal *)
Theorem check : (mult a (mult b (mult a c))) = (mult (mult (mult a b) a) c).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

