(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z -> Z.
Axiom right_inverse : forall X Y : Z, (multiply X Y (inverse Y)) =? X.
Axiom left_inverse : forall X Y : Z, (multiply (inverse Y) Y X) =? X.
Axiom ternary_multiply_2 : forall X Y : Z, (multiply X X Y) =? X.
Axiom ternary_multiply_1 : forall X Y : Z, (multiply Y X X) =? X.
Axiom associativity : forall V W X Y Z : Z, (multiply (multiply V W X) Y (multiply V W Z)) =? (multiply V W (multiply X Y Z)).

Add_lemmas right_inverse left_inverse ternary_multiply_2 ternary_multiply_1 associativity.

(* Zoal *)
Theorem check : (inverse (inverse a)) =? a.
Proof.
  smt.
Qed.

Check check.

