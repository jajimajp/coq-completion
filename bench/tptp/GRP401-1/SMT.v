(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable commutator : Z -> Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom commutator_distributes_over_product : forall A B C : Z, (commutator (multiply A B) C) = (multiply (commutator A C) (commutator B C)).
Axiom commutator : forall A B : Z, (multiply A B) = (multiply B (multiply A (commutator A B))).
