(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom single_axiom : forall A B C : Z, (inverse (multiply (inverse (multiply A (inverse (multiply (inverse B) (multiply (inverse C) (inverse (multiply (inverse C) C))))))) (multiply A C))) = B.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  smt.
Qed.

Check check.

