(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter op_l : G -> G -> G -> G.
Parameter op_r : G -> G -> G -> G.
Parameter op_t : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter s : G -> G.
Parameter unit : G.
Axiom c20 : forall A B C : G, (op_l (op_l A B C) B C) = A.
Axiom c19 : forall A B C : G, (op_r (op_r A B C) B C) = A.
Axiom c18 : forall A B : G, (op_t (op_t A B) B) = A.
Axiom c17 : forall A B C : G, (op_t (op_t A B) C) = (op_t (op_t A C) B).
Axiom c16 : forall A B C D : G, (op_t (op_l A B C) D) = (op_l (op_t A D) B C).
Axiom c15 : forall A B C D : G, (op_t (op_r A B C) D) = (op_r (op_t A D) B C).
Axiom c14 : forall A B C D E : G, (op_l (op_l A B C) D E) = (op_l (op_l A D E) B C).
Axiom c13 : forall A B C D E : G, (op_l (op_r A B C) D E) = (op_r (op_l A D E) B C).
Axiom c12 : forall A B C D E : G, (op_r (op_r A B C) D E) = (op_r (op_r A D E) B C).
Axiom c11 : forall A B : G, (op_t A B) = (ld B (mult A B)).
Axiom c10 : forall A B C : G, (op_r A B C) = (rd (mult (mult A B) C) (mult B C)).
Axiom c09 : forall A B C : G, (op_l A B C) = (ld (mult C B) (mult C (mult B A))).
Axiom c08 : forall A : G, (s (mult A A)) = A.
Axiom c07 : forall A : G, (mult (s A) (s A)) = A.
Axiom c06 : forall A B : G, (mult (rd A B) B) = A.
Axiom c05 : forall A B : G, (rd (mult A B) B) = A.
Axiom c04 : forall A B : G, (ld A (mult A B)) = B.
Axiom c03 : forall A B : G, (mult A (ld A B)) = B.
Axiom c02 : forall A : G, (mult A unit) = A.
Axiom c01 : forall A : G, (mult unit A) = A.


(* Goal *)
Theorem check : (mult (mult a b) c) = (mult a (mult b c)).
Proof.
  hammer.
Qed.

Check check.

