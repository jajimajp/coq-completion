(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable d : Z.
Variable h : Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable j : Z.
Variable k : Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_j_times_inverse_h_is_k : (multiply j (inverse h)) =? k.
Axiom ax_h_times_b_is_j : (multiply h b) =? j.
Axiom ax_d_times_inverse_b_is_h : (multiply d (inverse b)) =? h.
Axiom ax_c_times_inverse_a_is_d : (multiply c (inverse a)) =? d.
Axiom ax_a_times_b_is_c : (multiply a b) =? c.
Axiom ax_x_cubed_is_identity : forall X : Z, (multiply X (multiply X X)) =? identity.
Axiom ax_right_inverse : forall X : Z, (multiply X (inverse X)) =? identity.
Axiom ax_right_identity : forall X : Z, (multiply X identity) =? X.
Axiom ax_associativity : forall X Y Z : Z, (multiply (multiply X Y) Z) =? (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : Z, (multiply (inverse X) X) =? identity.
Axiom ax_left_identity : forall X : Z, (multiply identity X) =? X.

Add_lemmas ax_j_times_inverse_h_is_k ax_h_times_b_is_j ax_d_times_inverse_b_is_h ax_c_times_inverse_a_is_d ax_a_times_b_is_c ax_x_cubed_is_identity ax_right_inverse ax_right_identity ax_associativity ax_left_inverse ax_left_identity.

(* Goal *)
Theorem check : (multiply k (inverse b)) =? identity.
Proof.
  smt.
Qed.

Check check.

