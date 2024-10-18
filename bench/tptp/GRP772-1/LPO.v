(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G -> G -> G -> G.
Parameter c : G -> G -> G.
Parameter difference : G -> G -> G.
Parameter eta : G -> G.
Parameter i : G -> G.
Parameter j : G -> G.
Parameter one : G.
Parameter product : G -> G -> G.
Parameter quotient : G -> G -> G.
Parameter t : G -> G -> G.
Parameter x0 : G.
Parameter x1 : G.
Hint Resolve one.
Axiom ax_sos32 : forall A B C : G, (a (j A) B C) = (a B C A).
Axiom ax_sos31 : forall A B C : G, (a (i A) B C) = (a (j A) B C).
Axiom ax_sos30 : forall A B C : G, (a A (i B) C) = (a A (j B) C).
Axiom ax_sos29 : forall A B C : G, (product (a A B C) (difference C (product (a C A B) C))) = one.
Axiom ax_sos28 : forall A B C D E : G, (product (product A B) (a C D E)) = (product A (product B (a C D E))).
Axiom ax_sos27 : forall A B C D E : G, (product (a A B C) (product D E)) = (product (product (a A B C) D) E).
Axiom ax_sos26 : forall A B C D : G, (product (product A B) (c C D)) = (product A (product B (c C D))).
Axiom ax_sos25 : forall A B C D : G, (product (c A B) (product C D)) = (product (product (c A B) C) D).
Axiom ax_sos24 : forall A B : G, (product (product A B) (c B A)) = (product B A).
Axiom ax_sos23 : forall A B C : G, (product (product A (product B C)) (a A B C)) = (product (product A B) C).
Axiom ax_sos22 : forall A B : G, (product (j (j A)) (j (product B A))) = (j B).
Axiom ax_sos21 : forall A B : G, (product (i (product A B)) (i (i A))) = (i B).
Axiom ax_sos20 : forall A B C : G, (t (eta A) (product B C)) = (product (t (eta A) B) (t (eta A) C)).
Axiom ax_sos19 : forall A B : G, (t A B) = (quotient (product A B) A).
Axiom ax_sos18 : forall A B C : G, (product (product (product (quotient (j A) A) (product A A)) B) C) = (product (product (quotient (j A) A) (product A A)) (product B C)).
Axiom ax_sos17 : forall A : G, (quotient (j A) A) = (product (j A) (i A)).
Axiom ax_sos16 : forall A B C : G, (product (eta A) (product B C)) = (product (product (eta A) B) C).
Axiom ax_sos15 : forall A B : G, (product A (product B (eta A))) = (product (product A B) (eta A)).
Axiom ax_sos14 : forall A B : G, (product A (product (eta A) B)) = (product (j (j A)) B).
Axiom ax_sos13 : forall A B : G, (product (i (i A)) B) = (product (eta A) (product A B)).
Axiom ax_sos12 : forall A : G, (eta A) = (product (i A) A).
Axiom ax_sos11 : forall A : G, (product (i A) A) = (product A (j A)).
Axiom ax_sos10 : forall A : G, (j A) = (quotient one A).
Axiom ax_sos09 : forall A : G, (i A) = (difference A one).
Axiom ax_sos08 : forall A B C : G, (difference (product A B) (product A (product B C))) = (quotient (quotient (product C (product A B)) B) A).
Axiom ax_sos07 : forall A B C : G, (difference A (product (product A B) C)) = (quotient (product B (product C A)) A).
Axiom ax_sos06 : forall A B : G, (product (quotient A B) B) = A.
Axiom ax_sos05 : forall A B : G, (quotient (product A B) B) = A.
Axiom ax_sos04 : forall A B : G, (difference A (product A B)) = B.
Axiom ax_sos03 : forall A B : G, (product A (difference A B)) = B.
Axiom ax_sos02 : forall A : G, (product one A) = A.
Axiom ax_sos01 : forall A : G, (product A one) = A.

Complete ax_sos32 ax_sos31 ax_sos30 ax_sos29 ax_sos28 ax_sos27 ax_sos26 ax_sos25 ax_sos24 ax_sos23 ax_sos22 ax_sos21 ax_sos20 ax_sos19 ax_sos18 ax_sos17 ax_sos16 ax_sos15 ax_sos14 ax_sos13 ax_sos12 ax_sos11 ax_sos10 ax_sos09 ax_sos08 ax_sos07 ax_sos06 ax_sos05 ax_sos04 ax_sos03 ax_sos02 ax_sos01 : a c difference eta i j one product quotient t x0 x1 : hint
  for ((a x0 x1 x1) = (a x1 x1 x0)).

(* Goal *)
Theorem check : (a x0 x1 x1) = (a x1 x1 x0).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

