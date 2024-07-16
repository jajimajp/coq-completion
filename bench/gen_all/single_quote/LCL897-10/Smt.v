(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Axiom sos_08 : forall ' =? =?>' '+' A B : Z, ('+' A (' =? =?>' A B)) =? ('+' B (' =? =?>' B A)).
Axiom sos_07 : forall ' =? =?>' '+' A B C : Z, (' =? =?>' ('+' A B) C) =? (' =? =?>' A (' =? =?>' B C)).
Axiom sos_06 : forall ' =? =?>' '0' A : Z, (' =? =?>' '0' A) =? A.
Axiom sos_05 : forall ' =? =?>' '0' A : Z, (' =? =?>' A '0') =? '0'.
Axiom sos_04 : forall ' =? =?>' '0' A : Z, (' =? =?>' A A) =? '0'.
Axiom sos_03 : forall '+' '0' A : Z, ('+' A '0') =? A.
Axiom sos_02 : forall '+' A B : Z, ('+' A B) =? ('+' B A).
Axiom sos_01 : forall '+' A B C : Z, ('+' ('+' A B) C) =? ('+' A ('+' B C)).

Add_lemmas sos_08 sos_07 sos_06 sos_05 sos_04 sos_03 sos_02 sos_01.

(* Zoal *)
Theorem check : forall ' =? =?>' '+' : Z, ('+' ('+' a (' =? =?>' a b)) (' =? =?>' ('+' a (' =? =?>' a b)) c)) =? ('+' a (' =? =?>' a ('+' b (' =? =?>' b c)))).
Proof.
  smt.
Qed.

Check check.

