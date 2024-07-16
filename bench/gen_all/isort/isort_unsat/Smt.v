(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable cons : Z -> Z -> Z.
Variable false : Z.
Variable insert : Z -> Z -> Z.
Variable insert_if : Z -> Z -> Z -> Z.
Variable isort : Z -> Z.
Variable le : Z -> Z -> Z.
Variable nil : Z.
Variable s : Z -> Z.
Variable true : Z.
Variable z : Z.
Axiom insert_if_false : forall L X Y : Z, (insert_if false X (cons Y L)) =? (cons Y (insert X L)).
Axiom insert_if_true : forall L X Y : Z, (insert_if true X (cons Y L)) =? (cons X (cons Y L)).
Axiom insert_cons : forall L X Y : Z, (insert X (cons Y L)) =? (insert_if (le X Y) X (cons Y L)).
Axiom insert_nil : forall X : Z, (insert X nil) =? (cons X nil).
Axiom isort_cons : forall L X : Z, (isort (cons X L)) =? (insert X (isort L)).
Axiom isort_nil : (isort nil) =? nil.
Axiom le_s_s : forall X Y : Z, (le (s X) (s Y)) =? (le X Y).
Axiom le_s_z : forall X : Z, (le (s X) z) =? false.
Axiom le_z : forall Y : Z, (le z Y) =? true.

Add_lemmas insert_if_false insert_if_true insert_cons insert_nil isort_cons isort_nil le_s_s le_s_z le_z.

(* Zoal *)
Theorem check : (isort (cons (s (s z)) (cons (s (s (s z))) (cons (s z) nil)))) =? (cons (s z) (cons (s (s z)) (cons (s (s (s z))) nil))).
Proof.
  smt.
Qed.

Check check.

