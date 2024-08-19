(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable divide : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom identity : forall X : Z, identity = (divide X X).
Axiom inverse : forall X : Z, (inverse X) = (divide identity X).
Axiom multiply : forall X Y : Z, (multiply X Y) = (divide X (divide identity Y)).
Axiom single_axiom : forall X Y Z : Z, (divide X (divide (divide (divide (divide X X) Y) Z) (divide (divide identity X) Z))) = Y.

Add_lemmas identity inverse multiply single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  smt.
Qed.

Check check.

