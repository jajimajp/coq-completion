(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable one : Z.
Variable s : Z -> Z.
Variable sum : Z -> Z.
Variable times : Z -> Z -> Z.
Variable zero : Z.
Axiom induction_hypothesis : forall '+' : Z, ('+' (sum a) (sum a)) =? (times a (s a)).
Axiom sum_s : forall '+' N : Z, (sum (s N)) =? ('+' (s N) (sum N)).
Axiom sum_zero : (sum zero) =? zero.
Axiom times_s : forall '+' X Y : Z, (times (s X) Y) =? ('+' Y (times X Y)).
Axiom plus_s : forall '+' X Y : Z, ('+' (s X) Y) =? (s ('+' X Y)).
Axiom distr_001 : forall '+' X Y Z : Z, (times ('+' X Y) Z) =? ('+' (times X Z) (times Y Z)).
Axiom distr : forall '+' X Y Z : Z, (times X ('+' Y Z)) =? ('+' (times X Y) (times X Z)).
Axiom times_one : forall X : Z, (times X one) =? X.
Axiom times_zero : forall X : Z, (times X zero) =? zero.
Axiom plus_zero : forall '+' X : Z, ('+' X zero) =? X.
Axiom times_assoc : forall X Y Z : Z, (times X (times Y Z)) =? (times (times X Y) Z).
Axiom times_comm : forall X Y : Z, (times X Y) =? (times Y X).
Axiom plus_assoc : forall '+' X Y Z : Z, ('+' X ('+' Y Z)) =? ('+' ('+' X Y) Z).
Axiom plus_comm : forall '+' X Y : Z, ('+' X Y) =? ('+' Y X).

Add_lemmas induction_hypothesis sum_s sum_zero times_s plus_s distr_001 distr times_one times_zero plus_zero times_assoc times_comm plus_assoc plus_comm.

(* Zoal *)
Theorem check : forall '+' : Z, ('+' (sum (s a)) (sum (s a))) =? (times (s a) (s (s a))).
Proof.
  smt.
Qed.

Check check.

