(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable double_divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom multiply : forall A B : Z, (multiply A B) = (inverse (double_divide B A)).
Axiom single_axiom : forall A B C : Z, (inverse (double_divide (inverse (double_divide A (inverse (double_divide B (double_divide A C))))) C)) = B.

Add_lemmas multiply single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

