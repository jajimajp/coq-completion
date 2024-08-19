(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom associativity_of_commutator : forall A B C : Z, (commutator (commutator A B) C) = (commutator A (commutator B C)).
Axiom commutator : forall A B : Z, (multiply A B) = (multiply B (multiply A (commutator A B))).