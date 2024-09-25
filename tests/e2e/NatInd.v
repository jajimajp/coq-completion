Declare ML Module "coq-completion.plugin".
Require Import Setoid.

Inductive G : Set :=
  | O' : G
  | S' : G -> G.

Fixpoint plus' (n m : G) : G :=
  match n with
  | S' p => S' (plus' p m)
  | O' => m
  end.

(* DEBUG *)
Axiom plus'0 : forall m, plus' O' m = m.
Axiom plus'1 : forall n m, plus' (S' n) m = S' (plus' n m).

Theorem check : forall n : G, n = plus' n O'.
Proof.
  induction n.
  - compl_auto.
  - compl_auto.
Qed.

Print check.