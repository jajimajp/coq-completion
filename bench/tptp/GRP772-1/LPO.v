(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom sos32 : forall A B C : G, (a (j A) B C) = (a B C A).
Axiom sos31 : forall A B C : G, (a (i A) B C) = (a (j A) B C).
Axiom sos30 : forall A B C : G, (a A (i B) C) = (a A (j B) C).
Axiom sos29 : forall A B C : G, (product (a A B C) (difference C (product (a C A B) C))) = one.
Axiom sos28 : forall A B C D E : G, (product (product A B) (a C D E)) = (product A (product B (a C D E))).
Axiom sos27 : forall A B C D E : G, (product (a A B C) (product D E)) = (product (product (a A B C) D) E).
Axiom sos26 : forall A B C D : G, (product (product A B) (c C D)) = (product A (product B (c C D))).
Axiom sos25 : forall A B C D : G, (product (c A B) (product C D)) = (product (product (c A B) C) D).
Axiom sos24 : forall A B : G, (product (product A B) (c B A)) = (product B A).
Axiom sos23 : forall A B C : G, (product (product A (product B C)) (a A B C)) = (product (product A B) C).
Axiom sos22 : forall A B : G, (product (j (j A)) (j (product B A))) = (j B).
Axiom sos21 : forall A B : G, (product (i (product A B)) (i (i A))) = (i B).
Axiom sos20 : forall A B C : G, (t (eta A) (product B C)) = (product (t (eta A) B) (t (eta A) C)).
Axiom sos19 : forall A B : G, (t A B) = (quotient (product A B) A).
Axiom sos18 : forall A B C : G, (product (product (product (quotient (j A) A) (product A A)) B) C) = (product (product (quotient (j A) A) (product A A)) (product B C)).
Axiom sos17 : forall A : G, (quotient (j A) A) = (product (j A) (i A)).
Axiom sos16 : forall A B C : G, (product (eta A) (product B C)) = (product (product (eta A) B) C).
Axiom sos15 : forall A B : G, (product A (product B (eta A))) = (product (product A B) (eta A)).
Axiom sos14 : forall A B : G, (product A (product (eta A) B)) = (product (j (j A)) B).
Axiom sos13 : forall A B : G, (product (i (i A)) B) = (product (eta A) (product A B)).
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

Complete sos32 sos31 sos30 sos29 sos28 sos27 sos26 sos25 sos24 sos23 sos22 sos21 sos20 sos19 sos18 sos17 sos16 sos15 sos14 sos13 sos12 sos11 sos10 sos09 sos08 sos07 sos06 sos05 sos04 sos03 sos02 sos01 :  : hint
  for ((a x0 x1 x1) = (a x1 x1 x0)).

(* Goal *)
Theorem check : (a x0 x1 x1) = (a x1 x1 x0).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

