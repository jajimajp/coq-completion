(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter asoc : G -> G -> G -> G.
Parameter i : G -> G.
Parameter mult : G -> G -> G.
Parameter op_l : G -> G -> G -> G.
Parameter op_r : G -> G -> G -> G.
Parameter op_t : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom c19 : forall A B C : G, (op_t (op_t A B) C) = (op_t (op_t A C) B).
Axiom c18 : forall A B C D : G, (op_t (op_l A B C) D) = (op_l (op_t A D) B C).
Axiom c17 : forall A B C D : G, (op_t (op_r A B C) D) = (op_r (op_t A D) B C).
Axiom c16 : forall A B C D E : G, (op_l (op_l A B C) D E) = (op_l (op_l A D E) B C).
Axiom c15 : forall A B C D E : G, (op_l (op_r A B C) D E) = (op_r (op_l A D E) B C).
Axiom c14 : forall A B C D E : G, (op_r (op_r A B C) D E) = (op_r (op_r A D E) B C).
Axiom c13 : forall A B : G, (op_t A B) = (mult (i B) (mult A B)).
Axiom c12 : forall A B C : G, (op_r A B C) = (rd (mult (mult A B) C) (mult B C)).
Axiom c11 : forall A B C : G, (op_l A B C) = (mult (i (mult C B)) (mult C (mult B A))).
Axiom c10 : forall A B C : G, (mult (mult A B) C) = (mult (mult A (mult B C)) (asoc A B C)).
Axiom c09 : forall A B C : G, (mult (mult A (mult B A)) C) = (mult A (mult B (mult A C))).
Axiom c08 : forall A B : G, (mult (rd A B) B) = A.
Axiom c07 : forall A B : G, (rd (mult A B) B) = A.
Axiom c06 : forall A B : G, (mult (i A) (mult A B)) = B.
Axiom c05 : forall A B : G, (i (mult A B)) = (mult (i A) (i B)).
Axiom c04 : forall A : G, (mult (i A) A) = unit.
Axiom c03 : forall A : G, (mult A (i A)) = unit.
Axiom c02 : forall A : G, (mult A unit) = A.
Axiom c01 : forall A : G, (mult unit A) = A.

Complete c19 c18 c17 c16 c15 c14 c13 c12 c11 c10 c09 c08 c07 c06 c05 c04 c03 c02 c01 : asoc i mult op_l op_r op_t rd unit : hint
  for ((asoc (asoc a b c) d e) = unit).

(* Goal *)
Theorem check : (asoc (asoc a b c) d e) = unit.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.
