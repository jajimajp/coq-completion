(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable double_divide : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom identity : forall X : Z, identity = (double_divide X (inverse X)).
Axiom inverse : forall X : Z, (inverse X) = (double_divide X identity).
Axiom multiply : forall X Y : Z, (multiply X Y) = (double_divide (double_divide Y X) identity).
Axiom single_axiom : forall X Y Z : Z, (double_divide (double_divide identity X) (double_divide identity (double_divide (double_divide (double_divide X Y) identity) (double_divide Z Y)))) = Z.

Add_lemmas identity inverse multiply single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  smt.
Qed.

Check check.

