(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable difference : Z -> Z -> Z.
Variable eta : Z -> Z.
Variable i : Z -> Z.
Variable j : Z -> Z.
Variable one : Z.
Variable product : Z -> Z -> Z.
Variable quotient : Z -> Z -> Z.
Variable x0 : Z.
Variable x1 : Z.
Axiom ax_sos12 : forall A : Z, (eta A) = (product (i A) A).
Axiom ax_sos11 : forall A : Z, (product (i A) A) = (product A (j A)).
Axiom ax_sos10 : forall A : Z, (j A) = (quotient one A).
Axiom ax_sos09 : forall A : Z, (i A) = (difference A one).
Axiom ax_sos08 : forall A B C : Z, (difference (product A B) (product A (product B C))) = (quotient (quotient (product C (product A B)) B) A).
Axiom ax_sos07 : forall A B C : Z, (difference A (product (product A B) C)) = (quotient (product B (product C A)) A).
Axiom ax_sos06 : forall A B : Z, (product (quotient A B) B) = A.
Axiom ax_sos05 : forall A B : Z, (quotient (product A B) B) = A.
Axiom ax_sos04 : forall A B : Z, (difference A (product A B)) = B.
Axiom ax_sos03 : forall A B : Z, (product A (difference A B)) = B.
Axiom ax_sos02 : forall A : Z, (product one A) = A.
Axiom ax_sos01 : forall A : Z, (product A one) = A.

Add_lemmas ax_sos12 ax_sos11 ax_sos10 ax_sos09 ax_sos08 ax_sos07 ax_sos06 ax_sos05 ax_sos04 ax_sos03 ax_sos02 ax_sos01.

(* Goal *)
Theorem check : (product (i (i x0)) x1) = (product (eta x0) (product x0 x1)).
Proof.
  smt.
Qed.

Check check.

