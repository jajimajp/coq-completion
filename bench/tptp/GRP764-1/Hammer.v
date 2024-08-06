(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter difference : G -> G -> G.
Parameter eta : G -> G.
Parameter i : G -> G.
Parameter j : G -> G.
Parameter one : G.
Parameter product : G -> G -> G.
Parameter quotient : G -> G -> G.
Axiom sos12 : forall A : G, (eta A) = (product (i A) A).
Axiom sos11 : forall A : G, (product (i A) A) = (product A (j A)).
Axiom sos10 : forall A : G, (j A) = (quotient one A).
Axiom sos09 : forall A : G, (i A) = (difference A one).
Axiom sos08 : forall A B C : G, (difference (product A B) (product A (product B C))) = (quotient (quotient (product C (product A B)) B) A).
Axiom sos07 : forall A B C : G, (difference A (product (product A B) C)) = (quotient (product B (product C A)) A).
Axiom sos06 : forall A B : G, (product (quotient A B) B) = A.
Axiom sos05 : forall A B : G, (quotient (product A B) B) = A.
Axiom sos04 : forall A B : G, (difference A (product A B)) = B.
Axiom sos03 : forall A B : G, (product A (difference A B)) = B.
Axiom sos02 : forall A : G, (product one A) = A.
Axiom sos01 : forall A : G, (product A one) = A.


(* Goal *)
Theorem check : (product x0 (product (eta x0) x1)) = (product (j (j x0)) x1).
Proof.
  hammer.
Qed.

Check check.
