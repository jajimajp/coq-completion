(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom condition : forall X Y : Z, (multiply X (multiply X (multiply X (multiply Y Y)))) = (multiply Y (multiply X (multiply X (multiply Y X)))).
