(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a2 : Z.
Variable b2 : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_single_axiom : forall A B C D : Z, (inverse (multiply A (multiply B (multiply (multiply (inverse B) C) (inverse (multiply D (multiply A C))))))) = D.

Add_lemmas ax_single_axiom.

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  smt.
Qed.

Check check.

