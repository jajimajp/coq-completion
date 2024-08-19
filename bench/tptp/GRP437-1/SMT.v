(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom single_axiom : forall A B C D : Z, (multiply A (inverse (multiply B (multiply C (multiply (multiply (inverse C) (inverse (multiply D B))) A))))) = D.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  smt.
Qed.

Check check.

