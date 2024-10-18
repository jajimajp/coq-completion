(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter x6 : G.
Parameter x7 : G.
Parameter x8 : G.
Hint Resolve x6.
Axiom ax_f07 : forall A B : G, (ld A (mult A (ld B B))) = (rd (mult (rd A A) B) B).
Axiom ax_f06 : forall A B C D : G, (rd (mult (mult A B) (rd C D)) (rd C D)) = (mult A (rd (mult B D) D)).
Axiom ax_f05 : forall A B C D : G, (ld (ld A B) (mult (ld A B) (mult C D))) = (mult (ld A (mult A C)) D).
Axiom ax_f04 : forall A B : G, (mult (rd A B) B) = (rd (mult A B) B).
Axiom ax_f03 : forall A B : G, (mult A (ld A B)) = (ld A (mult A B)).
Axiom ax_f02 : forall A : G, (rd (mult A A) A) = A.
Axiom ax_f01 : forall A : G, (ld A (mult A A)) = A.

Complete ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 : ld mult rd x6 x7 x8 : hint
  for ((rd (mult x6 (ld x7 x8)) (ld x7 x8)) = (rd (mult x6 x8) x8)).

(* Goal *)
Theorem check : (rd (mult x6 (ld x7 x8)) (ld x7 x8)) = (rd (mult x6 x8) x8).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

