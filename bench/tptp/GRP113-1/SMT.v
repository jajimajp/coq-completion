(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_c_not_identity : c =? identity.
Axiom ax_b_not_identity : b =? identity.
Axiom ax_b_not_c : b =? c.
Axiom ax_a_not_identity : a =? identity.
Axiom ax_a_not_c : a =? c.
Axiom ax_a_not_b : a =? b.
Axiom ax_all_of_group1 : forall X : Z, X =? a.
Axiom ax_right_inverse : forall X : Z, (multiply X (inverse X)) =? identity.
Axiom ax_right_identity : forall X : Z, (multiply X identity) =? X.
Axiom ax_associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) =? (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : Z, (multiply (inverse X) X) =? identity.
Axiom ax_left_identity : forall X : Z, (multiply identity X) =? X.

Add_lemmas ax_c_not_identity ax_b_not_identity ax_b_not_c ax_a_not_identity ax_a_not_c ax_a_not_b ax_all_of_group1 ax_right_inverse ax_right_identity ax_associativity ax_left_inverse ax_left_identity.

(* Goal *)
Theorem check : (multiply a a) =? identity.
Proof.
  smt.
Qed.

Check check.

