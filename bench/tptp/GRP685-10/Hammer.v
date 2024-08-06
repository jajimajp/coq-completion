(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Axiom f07 : forall A B : G, (ld A (mult A (ld B B))) = (rd (mult (rd A A) B) B).
Axiom f06 : forall A B C D : G, (rd (mult (mult A B) (rd C D)) (rd C D)) = (mult A (rd (mult B D) D)).
Axiom f05 : forall A B C D : G, (ld (ld A B) (mult (ld A B) (mult C D))) = (mult (ld A (mult A C)) D).
Axiom f04 : forall A B : G, (mult (rd A B) B) = (rd (mult A B) B).
Axiom f03 : forall A B : G, (mult A (ld A B)) = (ld A (mult A B)).
Axiom f02 : forall A : G, (rd (mult A A) A) = A.
Axiom f01 : forall A : G, (ld A (mult A A)) = A.


(* Goal *)
Theorem check : (rd (mult x6 (ld x7 x8)) (ld x7 x8)) = (rd (mult x6 x8) x8).
Proof.
  hammer.
Qed.

Check check.
