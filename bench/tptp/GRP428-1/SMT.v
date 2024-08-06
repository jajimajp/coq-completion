(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom single_axiom : forall A B C D : Z, (multiply A (inverse (multiply (multiply (inverse (multiply (inverse B) (multiply (inverse A) C))) D) (inverse (multiply B D))))) = C.

Add_lemmas single_axiom.

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  smt.
Qed.

Check check.
