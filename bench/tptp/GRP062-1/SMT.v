(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a1 : Z.
Variable a2 : Z.
Variable a3 : Z.
Variable b1 : Z.
Variable b2 : Z.
Variable b3 : Z.
Variable c3 : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_single_axiom : forall U X Y Z : Z, (inverse (multiply X (multiply Y (multiply (multiply Z (inverse Z)) (inverse (multiply U (multiply X Y))))))) =? U.

Add_lemmas ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) =? (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

