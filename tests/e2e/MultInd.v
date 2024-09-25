Declare ML Module "coq-completion.plugin".
Require Import Setoid.

Inductive G : Set :=
  | O : G
  | S : G -> G.

Fixpoint plus (n m : G) : G :=
  match n with
  | S p => S (plus p m)
  | O => m
  end.

Fixpoint mult (n m : G) : G :=
  match n with
  | O => O
  | S p => plus (mult p m) m
  end.

Theorem check : forall n : G, O = mult n O.
Proof.
  induction n.
  - compl_auto plus.
  - compl_auto plus.
Qed.

Print check.