(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom multiply : forall A B : Z, (multiply A B) = (divide A (inverse B)).
Axiom single_axiom : forall A B C D : Z, (divide (inverse (divide A (divide B (divide C D)))) (divide (divide D C) A)) = B.

Add_lemmas multiply single_axiom.

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  smt.
Qed.

Check check.

