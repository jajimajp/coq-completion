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
Axiom ax_sos07 : forall A B C : G, (ld A (mult (mult A B) C)) = (rd (mult B (mult C A)) A).
Axiom ax_sos06 : forall A : G, (mult unit A) = A.
Axiom ax_sos05 : forall A : G, (mult A unit) = A.
Axiom ax_sos04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_sos03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_sos02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_sos01 : forall A B : G, (mult A (ld A B)) = B.

Complete ax_sos07 ax_sos06 ax_sos05 ax_sos04 ax_sos03 ax_sos02 ax_sos01 : a b c ld mult rd unit : hint
  for ((mult (mult (mult a a) b) c) = (mult (mult a a) (mult b c))).

(* Goal *)
Theorem check : (mult (mult (mult a a) b) c) = (mult (mult a a) (mult b c)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

