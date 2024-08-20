(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a1 : Z.
Variable a2 : Z.
Variable a3 : Z.
Variable b1 : Z.
Variable b2 : Z.
Variable b3 : Z.
Variable c3 : Z.
Variable double_divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_multiply : forall X Y : Z, (multiply X Y) = (inverse (double_divide Y X)).
Axiom ax_single_axiom : forall U X Y Z : Z, (double_divide (inverse X) (inverse (double_divide (inverse (double_divide X (double_divide Y Z))) (double_divide U (double_divide Y U))))) = Z.

Add_lemmas ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

