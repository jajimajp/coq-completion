(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)

Add_lemmas .

(* Zoal *)
Theorem check : forall X Y : Z, (f X) =? (f Y).
Proof.
  smt.
Qed.

Check check.

