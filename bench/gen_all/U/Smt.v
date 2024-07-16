(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z -> Z -> Z.
Variable i : Z.
Variable k : Z.
Variable s : Z.
Axiom i_definition : forall X : Z, (a i X) =? X.
Axiom k_definition : forall X Y : Z, (a (a k X) Y) =? X.
Axiom s_definition : forall X Y Z : Z, (a (a (a s X) Y) Z) =? (a (a X Z) (a Y Z)).

Add_lemmas i_definition k_definition s_definition.

(* Zoal *)
Theorem check : (a (a (a (a s (a k (a s i))) (a (a s i) i)) x) y) =? (a y (a (a x x) y)).
Proof.
  smt.
Qed.

Check check.

