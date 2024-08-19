(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom multiply : forall A B : Z, (multiply A B) = (inverse (double_divide B A)).
Axiom single_axiom : forall A B C D : Z, (double_divide (double_divide A (inverse (double_divide B C))) (double_divide (inverse B) (inverse (double_divide D (double_divide A D))))) = C.

Add_lemmas multiply single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  smt.
Qed.

Check check.

