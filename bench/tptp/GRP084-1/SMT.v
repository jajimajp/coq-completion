(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom single_axiom : forall U V W X Y Z : Z, (multiply (inverse (multiply (inverse (multiply (inverse (multiply X Y)) (multiply Y X))) (multiply (inverse (multiply Z U)) (multiply Z (inverse (multiply (multiply V (inverse W)) (inverse U))))))) W) = V.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

