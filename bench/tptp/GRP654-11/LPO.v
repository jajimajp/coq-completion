(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter x0 : G.
Parameter x1 : G.
Hint Resolve x0.
Axiom ax_f05 : forall A B C : G, (mult A (mult B (mult A C))) = (mult (mult (mult A B) A) C).
Axiom ax_f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : G, (mult A (ld A B)) = B.

Complete ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 : ld mult rd x0 x1 : hint
  for ((mult x0 (rd x1 x1)) = x0).

(* Goal *)
Theorem check : (mult x0 (rd x1 x1)) = x0.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

