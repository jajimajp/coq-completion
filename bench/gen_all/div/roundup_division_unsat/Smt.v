(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable div : Z -> Z -> Z.
Variable minus : Z -> Z -> Z.
Variable s : Z -> Z.
Variable z : Z.
Axiom div_s : forall X Y : Z, (div (s X) (s Y)) =? (s (div (minus X Y) (s Y))).
Axiom div_z : forall Y : Z, (div z (s Y)) =? z.
Axiom minus_s : forall X Y : Z, (minus (s X) (s Y)) =? (minus X Y).
Axiom minus_z_right : forall X : Z, (minus X z) =? X.
Axiom minus_z_left : forall Y : Z, (minus z Y) =? z.

Add_lemmas div_s div_z minus_s minus_z_right minus_z_left.

(* Zoal *)
Theorem check : (div (s z) (s (s z))) =? (s z).
Proof.
  smt.
Qed.

Check check.

