(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom single_axiom : forall A B C : Z, (multiply A (inverse (multiply (multiply (multiply (inverse B) B) (inverse (multiply (inverse (multiply A (inverse B))) C))) B))) = C.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  smt.
Qed.

Check check.

