(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable divide : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom identity : forall A : Z, identity = (divide A A).
Axiom inverse : forall A : Z, (inverse A) = (divide identity A).
Axiom multiply : forall A B : Z, (multiply A B) = (divide A (divide identity B)).
Axiom single_axiom : forall A B C : Z, (divide (divide identity (divide (divide (divide A B) C) A)) C) = B.

Add_lemmas identity inverse multiply single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  smt.
Qed.

Check check.

