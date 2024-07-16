(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable false : Z.
Variable gcd : Z -> Z -> Z.
Variable if_gcd : Z -> Z -> Z -> Z.
Variable le : Z -> Z -> Z.
Variable minus : Z -> Z -> Z.
Variable s : Z -> Z.
Variable true : Z.
Variable z : Z.
Axiom if_gcd_false : forall X Y : Z, (if_gcd false (s X) (s Y)) =? (gcd (minus Y X) (s X)).
Axiom if_gcd_true : forall X Y : Z, (if_gcd true (s X) (s Y)) =? (gcd (minus X Y) (s Y)).
Axiom gcd_s_s : forall X Y : Z, (gcd (s X) (s Y)) =? (if_gcd (le Y X) (s X) (s Y)).
Axiom gcd_s_z : forall X : Z, (gcd (s X) z) =? (s X).
Axiom gcd_z : forall Y : Z, (gcd z Y) =? Y.
Axiom minus_s_s : forall X Y : Z, (minus (s X) (s Y)) =? (minus X Y).
Axiom minus_z : forall X : Z, (minus X z) =? X.
Axiom le_s_s : forall X Y : Z, (le (s X) (s Y)) =? (le X Y).
Axiom le_s_z : forall X : Z, (le (s X) z) =? false.
Axiom le_z : forall Y : Z, (le z Y) =? true.

Add_lemmas if_gcd_false if_gcd_true gcd_s_s gcd_s_z gcd_z minus_s_s minus_z le_s_s le_s_z le_z.

(* Zoal *)
Theorem check : (gcd (s (s z)) (s z)) =? (s z).
Proof.
  smt.
Qed.

Check check.

