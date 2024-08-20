(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a3 : Z.
Variable b3 : Z.
Variable c3 : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_single_axiom : forall A B C D : Z, (multiply A (inverse (multiply (multiply (inverse (multiply (inverse B) (multiply (inverse A) C))) D) (inverse (multiply B D))))) = C.

Add_lemmas ax_single_axiom.

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  smt.
Qed.

Check check.

