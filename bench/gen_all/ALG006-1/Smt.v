(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable difference : Z -> Z -> Z.
Axiom set_difference_3 : forall X Y Z : Z, (difference (difference X Y) Z) =? (difference (difference X Z) (difference Y Z)).
Axiom set_difference_2 : forall X Y : Z, (difference X (difference X Y)) =? (difference Y (difference Y X)).
Axiom set_difference_1 : forall X Y : Z, (difference X (difference Y X)) =? X.

Add_lemmas set_difference_3 set_difference_2 set_difference_1.

(* Zoal *)
Theorem check : (difference (difference a c) b) =? (difference (difference a b) c).
Proof.
  smt.
Qed.

Check check.

