(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable add : Z -> Z -> Z.
Variable p : Z -> Z.
Variable s : Z -> Z.
Variable z : Z.
Axiom ps : forall X : Z, (p (s X)) =? X.
Axiom sp : forall X : Z, (s (p X)) =? X.
Axiom add_s : forall X Y : Z, (add (s X) Y) =? (s (add X Y)).
Axiom add_z : forall Y : Z, (add z Y) =? Y.

Add_lemmas ps sp add_s add_z.

(* Zoal *)
Theorem check : forall X Y : Z, (add (p X) Y) =? (p (add X Y)).
Proof.
  smt.
Qed.

Check check.

