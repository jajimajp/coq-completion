(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z -> Z -> Z.
Variable i : Z.
Variable k : Z.
Variable s : Z.
Variable x : Z.
Variable y : Z.
Axiom lem3 : (a (a (a s i) (a x x)) y) =? (a (a i y) (a (a x x) y)).
Axiom lem2 : (a (a (a s i) i) x) =? (a (a i x) (a i x)).
Axiom lem1 : (a (a (a s (a k (a s i))) (a (a s i) i)) x) =? (a (a (a k (a s i)) x) (a (a (a s i) i) x)).
Axiom i_definition : forall X : Z, (a i X) =? X.
Axiom k_definition : forall X Y : Z, (a (a k X) Y) =? X.
Axiom s_definition : forall X Y Z : Z, (a (a (a s X) Y) Z) =? (a (a X Z) (a Y Z)).

Add_lemmas lem3 lem2 lem1 i_definition k_definition s_definition.

(* Zoal *)
Theorem check : (a (a (a (a s (a k (a s i))) (a (a s i) i)) x) y) =? (a y (a (a x x) y)).
Proof.
  smt.
Qed.

Check check.

