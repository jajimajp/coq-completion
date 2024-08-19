(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom sos19 : forall A B C : G, (t (eta A) (product B C)) = (product (t (eta A) B) (t (eta A) C)).
Axiom sos18 : forall A B : G, (t A B) = (quotient (product A B) A).
Axiom sos17 : forall A B : G, (product A (product B (eta A))) = (product (product A B) (eta A)).
Axiom sos16 : forall A B : G, (product A (product (eta A) B)) = (product (j (j A)) B).
Axiom sos15 : forall A B : G, (product (i (i A)) B) = (product (eta A) (product A B)).
Axiom sos14 : forall A B C : G, (l A A (product B C)) = (product (l A A B) (l A A C)).
Axiom sos13 : forall A B C : G, (l A B C) = (difference (product A B) (product A (product B C))).
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
Theorem check : (product (eta x0) (product x1 x2)) = (product (product (eta x0) x1) x2).
Proof.
  hammer.
Qed.

Check check.

