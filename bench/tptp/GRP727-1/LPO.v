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
Parameter i : G -> G.
Parameter mult : G -> G -> G.
Parameter op_l : G -> G -> G -> G.
Parameter op_r : G -> G -> G -> G.
Parameter op_t : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Hint Resolve a.
Axiom ax_c20 : forall A B C D E : G, (asoc (asoc A B C) D E) = unit.
Axiom ax_c19 : forall A B C : G, (op_t (op_t A B) C) = (op_t (op_t A C) B).
Axiom ax_c18 : forall A B C D : G, (op_t (op_l A B C) D) = (op_l (op_t A D) B C).
Axiom ax_c17 : forall A B C D : G, (op_t (op_r A B C) D) = (op_r (op_t A D) B C).
Axiom ax_c16 : forall A B C D E : G, (op_l (op_l A B C) D E) = (op_l (op_l A D E) B C).
Axiom ax_c15 : forall A B C D E : G, (op_l (op_r A B C) D E) = (op_r (op_l A D E) B C).
Axiom ax_c14 : forall A B C D E : G, (op_r (op_r A B C) D E) = (op_r (op_r A D E) B C).
Axiom ax_c13 : forall A B : G, (op_t A B) = (mult (i B) (mult A B)).
Axiom ax_c12 : forall A B C : G, (op_r A B C) = (rd (mult (mult A B) C) (mult B C)).
Axiom ax_c11 : forall A B C : G, (op_l A B C) = (mult (i (mult C B)) (mult C (mult B A))).
Axiom ax_c10 : forall A B C : G, (mult (mult A B) C) = (mult (mult A (mult B C)) (asoc A B C)).
Axiom ax_c09 : forall A B C : G, (mult (mult A (mult B A)) C) = (mult A (mult B (mult A C))).
Axiom ax_c08 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_c07 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_c06 : forall A B : G, (mult (i A) (mult A B)) = B.
Axiom ax_c05 : forall A B : G, (i (mult A B)) = (mult (i A) (i B)).
Axiom ax_c04 : forall A : G, (mult (i A) A) = unit.
Axiom ax_c03 : forall A : G, (mult A (i A)) = unit.
Axiom ax_c02 : forall A : G, (mult A unit) = A.
Axiom ax_c01 : forall A : G, (mult unit A) = A.

Complete ax_c20 ax_c19 ax_c18 ax_c17 ax_c16 ax_c15 ax_c14 ax_c13 ax_c12 ax_c11 ax_c10 ax_c09 ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01 : a asoc b c d e i mult op_l op_r op_t rd unit : hint
  for ((asoc a b (asoc c d e)) = unit).

(* Goal *)
Theorem check : (asoc a b (asoc c d e)) = unit.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

