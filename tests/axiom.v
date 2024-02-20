Variable G : Set.
Variable f : G -> G -> G.
Variable e : G.

Axiom a : forall x, x = f e x.

Theorem t0 : forall x, f e x = x.
Proof.
  symmetry.
  apply a.
Qed.
