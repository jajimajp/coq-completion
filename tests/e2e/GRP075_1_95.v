(* --
Memo: This file tries to prove 95 from GRP075_1.v manually.

1: e2e_tests.GRP075_1.inverse(X0) <- e2e_tests.GRP075_1.double_divide(X0, e2e_tests.GRP075_1.identity()).
Proof: Axiom.

79: e2e_tests.GRP075_1.double_divide(e2e_tests.GRP075_1.double_divide(e2e_tests.GRP075_1.identity(), X5), X5) -> e2e_tests.GRP075_1.identity().
Proof: A critical pair between equations 64 and 63 with superposition e2e_tests.GRP075_1.double_divide(e2e_tests.GRP075_1.double_divide(X5, e2e_tests.GRP075_1.identity()), X5).

84: e2e_tests.GRP075_1.double_divide(e2e_tests.GRP075_1.identity(), e2e_tests.GRP075_1.identity()) <- e2e_tests.GRP075_1.double_divide(e2e_tests.GRP075_1.double_divide(e2e_tests.GRP075_1.identity(), X5), X5).
Proof: A critical pair between equations 78 and 72 with superposition e2e_tests.GRP075_1.double_divide(e2e_tests.GRP075_1.double_divide(e2e_tests.GRP075_1.identity(), e2e_tests.GRP075_1.double_divide(e2e_tests.GRP075_1.identity(), e2e_tests.GRP075_1.double_divide(X5, e2e_tests.GRP075_1.identity()))), X5).


95: e2e_tests.GRP075_1.inverse(e2e_tests.GRP075_1.identity()) -> e2e_tests.GRP075_1.identity().
Proof: Rewrite equation 84,
               lhs with equations [1]
               rhs with equations [79].

1: i (X0) <- double_divide (X0, e)
79: double_divide (double_divide (e, X5), X5) -> e
84: double_divide (e, e) <- double_divide (double_divide (e, X5), X5)
95: i (e) -> e
-- *)

Require Import Setoid.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter double_divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_identity : forall X : G, identity = (double_divide X (inverse X)).
Axiom ax_inverse : forall X : G, (inverse X) = (double_divide X identity).
Axiom ax_multiply : forall X Y : G, (multiply X Y) = (double_divide (double_divide Y X) identity).
Axiom ax_single_axiom : forall U X Y Z : G, (double_divide (double_divide (double_divide X (double_divide Y identity)) (double_divide (double_divide Z (double_divide U (double_divide U identity))) (double_divide X identity))) Y) = Z.

Hypothesis t1 : forall X0 : G, inverse X0 = double_divide X0 identity.
Hypothesis t79 : forall X5 : G, double_divide (double_divide identity X5) X5 = identity.
Hypothesis t84 : forall X5, double_divide identity identity = double_divide (double_divide identity X5) X5.

Ltac specialize_until_eq H x :=
  lazymatch type of H with
  | ?G -> ?Rest =>
      specialize (H x);
      specialize_until_eq H x
  | _ = _ => idtac
  | _ => fail "H is not of the form G -> ... or equality"
  end.

Create HintDb hint_a1.
Hint Resolve a1 : hint_a1.

Theorem t95 : inverse identity = identity.
Proof.
  pose proof (H := t84).
  rewrite_strat innermost <- t1 in H.
  rewrite_strat innermost t79 in H.
  (* auto using a1. *)
  (* specialize_until_eq H a1. *)
  debug auto with hint_a1.
  (* auto. *)
Qed.
