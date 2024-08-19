(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Variable sk_c1 : Z.
Variable sk_c2 : Z.
Variable sk_c3 : Z.
Variable sk_c4 : Z.
Variable sk_c5 : Z.
Variable sk_c6 : Z.
Variable sk_c7 : Z.
Axiom associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : Z, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : Z, (multiply identity X) = X.

Add_lemmas associativity left_inverse left_identity.

(* Goal *)
Theorem check : (multiply sk_c6 sk_c5) = sk_c7.
Proof.
  smt.
Qed.

Check check.

