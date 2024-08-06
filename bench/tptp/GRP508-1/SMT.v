(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom single_axiom : forall A B C D E F : Z, (multiply (inverse (multiply (inverse (multiply (inverse (multiply A B)) (multiply B A))) (multiply (inverse (multiply C D)) (multiply C (inverse (multiply (multiply E (inverse F)) (inverse D))))))) F) = E.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  smt.
Qed.

Check check.
