(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable e : Z.
Variable f : Z -> Z -> Z.
Variable i : Z -> Z.
Axiom associativity : forall X Y Z : Z, (f (f X Y) Z) =? (f X (f Y Z)).
Axiom right_inverse : forall X : Z, (f X (i X)) =? e.
Axiom right_unit : forall X : Z, (f X e) =? X.

Add_lemmas associativity right_inverse right_unit.

(* Zoal *)
Theorem check : forall X : Z, (f (i X) X) =? e.
Proof.
  smt.
Qed.

Check check.

