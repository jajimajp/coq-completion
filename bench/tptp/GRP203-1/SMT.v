(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable identity : Z.
Variable left_inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_moufang3 : forall X Y Z : Z, (multiply (multiply (multiply X Y) X) Z) =? (multiply X (multiply Y (multiply X Z))).
Axiom ax_left_inverse : forall X : Z, (multiply (left_inverse X) X) =? identity.
Axiom ax_left_identity : forall X : Z, (multiply identity X) =? X.

Add_lemmas ax_moufang3 ax_left_inverse ax_left_identity.

(* Goal *)
Theorem check : (multiply (multiply (multiply a b) c) b) =? (multiply a (multiply b (multiply c b))).
Proof.
  smt.
Qed.

Check check.

