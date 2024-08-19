(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Variable sk_c1 : Z.
Variable sk_c10 : Z.
Variable sk_c2 : Z.
Variable sk_c3 : Z.
Variable sk_c4 : Z.
Variable sk_c5 : Z.
Variable sk_c6 : Z.
Variable sk_c7 : Z.
Variable sk_c8 : Z.
Variable sk_c9 : Z.
Axiom associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : Z, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : Z, (multiply identity X) = X.

Add_lemmas associativity left_inverse left_identity.

(* Goal *)
Theorem check : (inverse sk_c10) = sk_c9.
Proof.
  smt.
Qed.

Check check.

