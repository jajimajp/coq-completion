(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter f : G -> G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter op_c : G.
Parameter rd : G -> G -> G.
Axiom c07 : forall A B : G, (f A B) = (mult (rd A op_c) (ld op_c B)).
Axiom c06 : forall A B C : G, (mult (mult A B) C) = (mult (mult A (rd C C)) (mult B C)).
Axiom c05 : forall A B C : G, (mult A (mult B C)) = (mult (mult A B) (mult (ld A A) C)).
Axiom c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom c01 : forall A B : G, (mult A (ld A B)) = B.

Complete c07 c06 c05 c04 c03 c02 c01 : f ld mult op_c rd : hint
  for ((f a (f b (f a c))) = (f (f (f a b) a) c)).

(* Goal *)
Theorem check : (f a (f b (f a c))) = (f (f (f a b) a) c).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

