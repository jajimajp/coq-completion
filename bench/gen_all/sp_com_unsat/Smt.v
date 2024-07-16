(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable add : Z -> Z -> Z.
Variable p : Z -> Z.
Variable s : Z -> Z.
Variable z : Z.
Axiom add_com : forall X Y : Z, (add X Y) =? (add Y X).
Axiom add_s : forall X Y : Z, (add (s X) Y) =? (s (add X Y)).
Axiom add_z : forall Y : Z, (add z Y) =? Y.
Axiom ps : forall X : Z, (p (s X)) =? X.
Axiom sp : forall X : Z, (s (p X)) =? X.

Add_lemmas add_com add_s add_z ps sp.

(* Zoal *)
Theorem check : (add (s z) (p z)) =? z.
Proof.
  smt.
Qed.

Check check.

