Declare ML Module "coq-completion.plugin".
(* From Completion Require Import Plugin. *)

Require Import Coq.Setoids.Setoid.

Parameter S : Set.
(* Parameter a : S *)
Parameter multiply : S -> S -> S.
Parameter identity : S.

(*
LPO with precedence: e2e_tests.GRP115_1.a > e2e_tests.GRP115_1.multiply > e2e_tests.GRP115_1.identity
axioms:
0: e2e_tests.GRP115_1.multiply(X0, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X0, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X0, X1), X2)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X2, X2)))) = X1.
generated rules:
0: e2e_tests.GRP115_1.multiply(X0, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X0, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X0, X1), X2)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X2, X2)))) -> X1.
Proof: Axiom.

2: e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, X4), X5) = e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(X4, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X5, X5)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X5, X5)))))).
Proof: A critical pair between equations 0 and 0 with superposition e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, X4), X5)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X5, X5)))), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X5, X5)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X5, X5)))))).

3: e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, X4), X5)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X5, X5))) = e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(X4, X2)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X2, X2)))).
Proof: A critical pair between equations 0 and 0 with superposition e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X3, X4), X5)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X5, X5)))), X2)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X2, X2)))).

6: e2e_tests.GRP115_1.multiply(X0, e2e_tests.GRP115_1.multiply(X0, e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.multiply(X0, e2e_tests.GRP115_1.multiply(X1, X2)), e2e_tests.GRP115_1.multiply(e2e_tests.GRP115_1.identity(), e2e_tests.GRP115_1.multiply(X2, X2))))) -> X1.
Proof: Rewrite equation 0,
- lhs by equation 3 L->R at [1]
*)

Axiom t0 : forall X0 X1 X2, (multiply X0 (multiply (multiply X0 (multiply (multiply X0 X1) X2)) (multiply identity (multiply X2 X2)))) = X1.
Axiom t3 : forall X2 X3 X4 X5,
  (multiply (multiply X3 (multiply (multiply X3 X4) X5)) (multiply identity (multiply X5 X5)))
= (multiply X3 (multiply (multiply X3 (multiply X4 X2)) (multiply identity (multiply X2 X2)))).


Theorem t6 : forall X0 X1 X2, (multiply X0 (multiply X0 (multiply (multiply X0 (multiply X1 X2)) (multiply identity (multiply X2 X2))))) = X1.
  pose proof t0.
  rewrite_pos lhs -> t3 at 1 in H.
  apply H.
Qed.

Axiom t24 : forall X3 X4 X7,
  multiply (multiply X3 X4) (multiply identity X7) = multiply X3 (multiply X4 X7).
Axiom t30 : forall X1 X2 X8,
  X1
  = multiply X8
             (multiply X8
                       ((multiply X8 (multiply (multiply X1 X2) (multiply X2 X2))))).
Axiom t35 : forall X0 X9 X10,
  multiply X9 identity
  = multiply X0
      (multiply X0
         ((multiply (multiply X0 (multiply X9 X10)) (multiply identity (multiply X10 X10))))).

(*
 39: e2e_tests.GRP115_1.multiply(X9, e2e_tests.GRP115_1.identity()) -> X9.
Proof: Rewrite equation 35,
- rhs by equation 24 L->R at [1,1]
- rhs by equation 30 L->R at []
 *)
Theorem t39 : forall X9, (multiply X9 identity) = X9.
  pose proof t35.
  rewrite_pos rhs -> t24 at 1 1 in H.
  rewrite_pos rhs <- t30 in H.
  (* rewrite_pos lhs H. *)
  auto.
  (* apply identity. *)
Qed.
