(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable add : Z -> Z -> Z.
Variable s : Z -> Z.
Variable z : Z.
Axiom add_s : forall X Y : Z, (add (s X) Y) =? (s (add X Y)).
Axiom add_z : forall Y : Z, (add z Y) =? Y.

Add_lemmas add_s add_z.

(* Zoal *)
Theorem check : (add (add (s z) z) z) =? (s z).
Proof.
  smt.
Qed.

Check check.

