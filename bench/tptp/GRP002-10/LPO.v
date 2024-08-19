(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter d : G.
Parameter h : G.
Parameter identity : G.
Parameter ifeq : G -> G -> G -> G -> G.
Parameter ifeq2 : G -> G -> G -> G -> G.
Parameter inverse : G -> G.
Parameter j : G.
Parameter k : G.
Parameter multiply : G -> G -> G.
Parameter product : G -> G -> G -> G.
Parameter true : G.
Axiom x_cubed_is_identity_2 : forall X Y : G, (ifeq (product X X Y) true (product Y X identity) true) = true.
Axiom x_cubed_is_identity_1 : forall X Y : G, (ifeq (product X X Y) true (product X Y identity) true) = true.
Axiom associativity2 : forall U V W X Y Z : G, (ifeq (product Y Z V) true (ifeq (product X V W) true (ifeq (product X Y U) true (product U Z W) true) true) true) = true.
Axiom associativity1 : forall U V W X Y Z : G, (ifeq (product U Z W) true (ifeq (product Y Z V) true (ifeq (product X Y U) true (product X V W) true) true) true) = true.
Axiom total_function2 : forall W X Y Z : G, (ifeq2 (product X Y W) true (ifeq2 (product X Y Z) true Z W) W) = W.
Axiom total_function1 : forall X Y : G, (product X Y (multiply X Y)) = true.
Axiom right_inverse : forall X : G, (product X (inverse X) identity) = true.
Axiom left_inverse : forall X : G, (product (inverse X) X identity) = true.
Axiom right_identity : forall X : G, (product X identity X) = true.
Axiom left_identity : forall X : G, (product identity X X) = true.
Axiom ifeq_axiom_001 : forall A B C : G, (ifeq A A B C) = B.
Axiom ifeq_axiom : forall A B C : G, (ifeq2 A A B C) = B.

Complete x_cubed_is_identity_2 x_cubed_is_identity_1 associativity2 associativity1 total_function2 total_function1 right_inverse left_inverse right_identity left_identity ifeq_axiom_001 ifeq_axiom : a b c d h identity ifeq ifeq2 inverse j k multiply product true : hint
  for ((product a b c) = true).

(* Goal *)
Theorem check : (product a b c) = true.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

