(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom single_axiom : forall A B C D : Z, (multiply A (inverse (multiply B (multiply C (multiply (multiply (inverse C) (inverse (multiply D B))) A))))) = D.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

