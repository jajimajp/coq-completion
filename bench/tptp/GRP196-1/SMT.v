(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_condition : forall X Y : Z, (multiply X (multiply Y (multiply Y Y))) =? (multiply Y (multiply Y (multiply Y X))).
Axiom ax_associativity_of_multiply : forall X Y Z : Z, (multiply (multiply X Y) Z) =? (multiply X (multiply Y Z)).

Add_lemmas ax_condition ax_associativity_of_multiply.

(* Goal *)
Theorem check : (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a b))))))))))))))))) =? (multiply a (multiply a (multiply a (multiply a (multiply a (multiply a (multiply a (multiply a (multiply a (multiply b (multiply b (multiply b (multiply b (multiply b (multiply b (multiply b (multiply b b))))))))))))))))).
Proof.
  smt.
Qed.

Check check.

