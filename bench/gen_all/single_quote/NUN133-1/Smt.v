(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable cubes : Z -> Z.
Variable one : Z.
Variable s : Z -> Z.
Variable sum : Z -> Z.
Variable times : Z -> Z -> Z.
Variable zero : Z.
Axiom induction_hypothesis : (times (sum a) (sum a)) =? (cubes a).
Axiom plus_sum : forall '+' N : Z, ('+' (sum N) (sum N)) =? (times N (s N)).
Axiom cubes_s : forall '+' N : Z, (cubes (s N)) =? ('+' (times (s N) (times (s N) (s N))) (cubes N)).
Axiom cubes_zero : (cubes zero) =? zero.
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

Add_lemmas induction_hypothesis plus_sum cubes_s cubes_zero sum_s sum_zero times_s plus_s distr_001 distr times_one times_zero plus_zero times_assoc times_comm plus_assoc plus_comm.

(* Zoal *)
Theorem check : (times (sum (s a)) (sum (s a))) =? (cubes (s a)).
Proof.
  smt.
Qed.

Check check.

