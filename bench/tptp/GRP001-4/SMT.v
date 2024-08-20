(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable identity : Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_a_times_b_is_c : (multiply a b) =? c.
Axiom ax_squareness : forall X : Z, (multiply X X) =? identity.
Axiom ax_left_identity : forall X : Z, (multiply identity X) =? X.
Axiom ax_associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) =? (multiply X (multiply Y Z)).

Add_lemmas ax_a_times_b_is_c ax_squareness ax_left_identity ax_associativity.

(* Goal *)
Theorem check : (multiply b a) =? c.
Proof.
  smt.
Qed.

Check check.

