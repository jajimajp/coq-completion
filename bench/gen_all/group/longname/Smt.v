(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable e : Z.
Variable ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff : Z -> Z -> Z.
Variable i : Z -> Z.
Axiom associativity : forall X Y Z : Z, (ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff X Y) Z) =? (ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff X (ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff Y Z)).
Axiom right_inverse : forall X : Z, (ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff X (i X)) =? e.
Axiom right_unit : forall X : Z, (ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff X e) =? X.

Add_lemmas associativity right_inverse right_unit.

(* Zoal *)
Theorem check : (i e) =? e.
Proof.
  smt.
Qed.

Check check.

