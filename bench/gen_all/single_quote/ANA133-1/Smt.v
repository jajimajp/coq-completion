(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable cos : Z -> Z.
Variable d : Z -> Z.
Variable minus : Z -> Z.
Variable one : Z.
Variable sin : Z -> Z.
Variable times : Z -> Z -> Z.
Variable x : Z.
Variable zero : Z.
Axiom derivative_of_cos : forall T : Z, (d (cos T)) =? (minus (times (sin T) (d T))).
Axiom derivative_of_sin : forall T : Z, (d (sin T)) =? (times (cos T) (d T)).
Axiom derivative_of_times : forall '+' T U : Z, (d (times T U)) =? ('+' (times T (d U)) (times U (d T))).
Axiom derivative_of_plus : forall '+' T U : Z, (d ('+' T U)) =? ('+' (d T) (d U)).
Axiom derivative_of_x : (d x) =? one.
Axiom derivative_of_one : (d one) =? zero.
Axiom derivative_of_zero : (d zero) =? zero.
Axiom minus : forall '+' X : Z, ('+' X (minus X)) =? zero.
Axiom distributivity : forall '+' X Y Z : Z, (times X ('+' Y Z)) =? ('+' (times X Y) (times X Z)).
Axiom times_one : forall X : Z, (times one X) =? X.
Axiom times_zero : forall X : Z, (times zero X) =? zero.
Axiom plus_zero : forall '+' X : Z, ('+' zero X) =? X.
Axiom associativity_of_times : forall X Y Z : Z, (times X (times Y Z)) =? (times (times X Y) Z).
Axiom commutativity_of_times : forall X Y : Z, (times X Y) =? (times Y X).
Axiom associtivity_of_plus : forall '+' X Y Z : Z, ('+' X ('+' Y Z)) =? ('+' ('+' X Y) Z).
Axiom commutativity_of_plus : forall '+' X Y : Z, ('+' X Y) =? ('+' Y X).

Add_lemmas derivative_of_cos derivative_of_sin derivative_of_times derivative_of_plus derivative_of_x derivative_of_one derivative_of_zero minus distributivity times_one times_zero plus_zero associativity_of_times commutativity_of_times associtivity_of_plus commutativity_of_plus.

(* Zoal *)
Theorem check : forall T : Z, (d T) =? (times x (cos x)).
Proof.
  smt.
Qed.

Check check.

