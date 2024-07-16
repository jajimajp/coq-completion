(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable cons : Z -> Z -> Z.
Variable last : Z -> Z -> Z.
Variable nil : Z.
Variable rev : Z -> Z.
Variable rev2 : Z -> Z -> Z.
Variable s : Z -> Z.
Variable z : Z.
Axiom rev2_cons : forall L X Y : Z, (rev2 X (cons Y L)) =? (rev (cons X (rev2 Y L))).
Axiom rev2_nil : forall X : Z, (rev2 X nil) =? nil.
Axiom last_cons : forall L X Y : Z, (last X (cons Y L)) =? (last Y L).
Axiom last_sX_nil : forall X : Z, (last (s X) nil) =? (s X).
Axiom last_z_nil : (last z nil) =? z.
Axiom rev_cons : forall L X : Z, (rev (cons X L)) =? (cons (last X L) (rev2 X L)).
Axiom rev_nil : (rev nil) =? nil.

Add_lemmas rev2_cons rev2_nil last_cons last_sX_nil last_z_nil rev_cons rev_nil.

(* Zoal *)
Theorem check : (rev (cons z (cons (s z) nil))) =? (cons (s z) (cons z nil)).
Proof.
  smt.
Qed.

Check check.

