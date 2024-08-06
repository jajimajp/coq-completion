(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom sos07 : forall A B C : G, (ld A (mult (mult A B) C)) = (rd (mult B (mult C A)) A).
Axiom sos06 : forall A : G, (mult unit A) = A.
Axiom sos05 : forall A : G, (mult A unit) = A.
Axiom sos04 : forall A B : G, (rd (mult A B) B) = A.
Axiom sos03 : forall A B : G, (mult (rd A B) B) = A.
Axiom sos02 : forall A B : G, (ld A (mult A B)) = B.
Axiom sos01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult (mult (mult a a) b) c) = (mult (mult a a) (mult b c)).
Proof.
  hammer.
Qed.

Check check.
