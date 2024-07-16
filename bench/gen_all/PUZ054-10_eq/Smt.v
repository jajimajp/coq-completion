(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable p : Z -> Z -> Z.
Variable s : Z -> Z.
Axiom two_different_balls_out_one_white_in : forall X Y : Z, (p (s X) (s Y)) =? (p (s X) Y).
Axiom two_blacks_out_one_black_in : forall X Y : Z, (p X (s (s Y))) =? (p X (s Y)).
Axiom two_whites_out_one_black_in : forall X Y : Z, (p (s (s X)) Y) =? (p X (s Y)).

Add_lemmas two_different_balls_out_one_white_in two_blacks_out_one_black_in two_whites_out_one_black_in.

(* Zoal *)
Theorem check : (p (s (s (s (s (s (s (s (s (s (s n0)))))))))) (s (s (s (s (s (s (s (s (s n0)))))))))) =? (p (s n0) n0).
Proof.
  smt.
Qed.

Check check.

