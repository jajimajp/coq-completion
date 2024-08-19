(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom identity : forall A : Z, identity = (divide A A).
Axiom inverse : forall A : Z, (inverse A) = (divide identity A).
Axiom multiply : forall A B : Z, (multiply A B) = (divide A (divide identity B)).
Axiom single_axiom : forall A B C : Z, (divide (divide identity (divide A (divide B (divide (divide (divide A A) A) C)))) C) = B.

Add_lemmas identity inverse multiply single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  smt.
Qed.

Check check.

