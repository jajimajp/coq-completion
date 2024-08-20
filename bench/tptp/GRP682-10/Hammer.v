(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter x0 : G.
Parameter x1 : G.
Parameter x2 : G.
Axiom ax_f07 : forall A B : G, (ld A (mult A (ld B B))) = (rd (mult (rd A A) B) B).
Axiom ax_f06 : forall A B C D : G, (rd (mult (mult A B) (rd C D)) (rd C D)) = (mult A (rd (mult B D) D)).
Axiom ax_f05 : forall A B C D : G, (ld (ld A B) (mult (ld A B) (mult C D))) = (mult (ld A (mult A C)) D).
Axiom ax_f04 : forall A B : G, (mult (rd A B) B) = (rd (mult A B) B).
Axiom ax_f03 : forall A B : G, (mult A (ld A B)) = (ld A (mult A B)).
Axiom ax_f02 : forall A : G, (rd (mult A A) A) = A.
Axiom ax_f01 : forall A : G, (ld A (mult A A)) = A.


(* Goal *)
Theorem check : (ld (ld x0 x1) (mult (ld x0 x1) x2)) = (ld x0 (mult x0 x2)).
Proof.
  hammer.
Qed.

Check check.

