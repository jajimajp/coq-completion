(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a3 : Z.
Variable b3 : Z.
Variable c3 : Z.
Variable divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_multiply : forall A B : Z, (multiply A B) =? (divide A (inverse B)).
Axiom ax_single_axiom : forall A B C D : Z, (divide (divide A A) (divide B (divide (divide C (divide D B)) (inverse D)))) =? C.

Add_lemmas ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) =? (multiply a3 (multiply b3 c3)).
Proof.
  smt.
Qed.

Check check.

