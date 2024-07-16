(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z -> Z -> Z.
Variable k : Z.
Variable s : Z.
Axiom k_definition : forall X Y : Z, (a (a k X) Y) =? X.
Axiom s_definition : forall X Y Z : Z, (a (a (a s X) Y) Z) =? (a (a X Z) (a Y Z)).

Add_lemmas k_definition s_definition.

(* Zoal *)
Theorem check : (a (a (a s k) k) x) =? x.
Proof.
  smt.
Qed.

Check check.

