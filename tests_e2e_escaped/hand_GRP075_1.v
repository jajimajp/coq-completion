Declare ML Module "coq-completion.plugin".
(* From Completion Require Import Plugin. *)

Require Import Setoid.

Parameter S : Set.
Parameter identity : S.
Parameter inverse : S -> S.
Parameter double_divide : S -> S -> S.

Hint Resolve identity.

Axiom t1 : forall X0, inverse X0 = double_divide X0 identity.
Axiom t79 : forall X5, double_divide (double_divide identity X5) X5 = identity.
Axiom t84 : forall X5,
    double_divide identity identity  = double_divide (double_divide identity X5) X5.
(*
95: e2e_tests.GRP075_1.inverse(e2e_tests.GRP075_1.identity()) -> e2e_tests.GRP075_1.identity().
Proof: Rewrite equation 84,
- lhs by equation 1 L->R at []
- rhs by equation 79 L->R at []
 *)
Theorem t95 : inverse identity = identity.
  intros.
  pose proof t84.
  rewrite_pos lhs <- t1 in H.
  rewrite_pos rhs t79 in H.
  auto.
Qed.
