(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom multiply : forall A B : Z, (multiply A B) = (divide A (inverse B)).
Axiom single_axiom : forall A B C : Z, (divide (divide (divide A (inverse B)) C) (divide A C)) = B.

Add_lemmas multiply single_axiom.

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  smt.
Qed.

Check check.

