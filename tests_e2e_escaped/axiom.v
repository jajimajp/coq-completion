Declare ML Module "coq-completion.plugin".

Parameter G : Set.
Parameter f : G -> G -> G.
Parameter e : G.

Axiom a : forall x, x = f e x.

Theorem t0 : forall x, f e x = x.
Proof.
  symmetry.
  apply a.
Qed.
