(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable add : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable s : Z -> Z.
Variable z : Z.
Axiom mult_s : forall X Y : Z, (mult (s X) Y) =? (add (mult X Y) Y).
Axiom mult_z : forall Y : Z, (mult z Y) =? z.
Axiom add_s : forall X Y : Z, (add (s X) Y) =? (s (add X Y)).
Axiom add_z : forall Y : Z, (add z Y) =? Y.

Add_lemmas mult_s mult_z add_s add_z.

(* Zoal *)
Theorem check : (mult (s (s z)) (s (s z))) =? (s (s (s (s z)))).
Proof.
  smt.
Qed.

Check check.

