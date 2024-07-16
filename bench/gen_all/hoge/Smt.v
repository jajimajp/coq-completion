(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable d : Z.
Variable f : Z -> Z.
Axiom a_is_c : a =? c.
Axiom cd : (f c) =? d.
Axiom ab : (f a) =? b.

Add_lemmas a_is_c cd ab.

(* Zoal *)
Theorem check : (f a) =? d.
Proof.
  smt.
Qed.

Check check.

