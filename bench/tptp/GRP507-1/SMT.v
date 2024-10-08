(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a3 : Z.
Variable b3 : Z.
Variable c3 : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_single_axiom : forall A B C D E F : Z, (multiply (inverse (multiply (inverse (multiply (inverse (multiply A B)) (multiply B A))) (multiply (inverse (multiply C D)) (multiply C (inverse (multiply (multiply E (inverse F)) (inverse D))))))) F) =? E.

Add_lemmas ax_single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) =? (multiply a3 (multiply b3 c3)).
Proof.
  smt.
Qed.

Check check.

