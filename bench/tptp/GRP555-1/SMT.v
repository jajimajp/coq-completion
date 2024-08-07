(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom multiply : forall A B : Z, (multiply A B) = (divide A (inverse B)).
Axiom single_axiom : forall A B C : Z, (divide (divide A (inverse (divide B (divide A C)))) C) = B.

Add_lemmas multiply single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  smt.
Qed.

Check check.

