(* Prove commonoid example with rewrite_pos *)
Require Import Coq.Setoids.Setoid.

Declare ML Module "coq-completion.plugin".
(* From Completion Require Import Plugin. *)

Parameter S : Set.
Parameter e : S.
Parameter c1 : S.
Parameter c2 : S.
Parameter f : S -> S -> S.

Axiom t2 : forall X0 X1 X2, f (f X0 X1) X2 = f X0 (f X1 X2).

(* 10: e2e_tests.braid.f(
         e2e_tests.braid.c2(),
         e2e_tests.braid.f(
           e2e_tests.braid.f(
             e2e_tests.braid.c1(),
             e2e_tests.braid.c2()), X2))
     <- e2e_tests.braid.f(
          e2e_tests.braid.f(
            e2e_tests.braid.c1(),
            e2e_tests.braid.f(
              e2e_tests.braid.c2(),
              e2e_tests.braid.c1())),
          X2). *)
Axiom t10 : forall X2, f c2 (f (f c1 c2) X2) = f (f c1 (f c2 c1)) X2.

(*
11: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), X2))) -> e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), X2))).
Proof: Rewrite equation 10,
- lhs by equation 2 L->R at [1]
- rhs by equation 2 L->R at []
- rhs by equation 2 L->R at [1]
*)
Theorem t11 : forall X2, f c2 (f c1 (f c2 X2)) = f c1 (f c2 (f c1 X2)).
  pose proof t10.
  rewrite_pos lhs -> t2 at 1 in H.
  rewrite_pos rhs -> t2 in H.
  rewrite_pos rhs -> t2 at 1 in H.
  apply H.
Qed.

(*
Completed
order:
LPO with precedence: ___false > ___true > e2e_tests.braid.e > e2e_tests.braid.c2 > e2e_tests.braid.c1 > e2e_tests.braid.f
axioms:
0: e2e_tests.braid.f(e2e_tests.braid.e(), X0) = X0.
1: e2e_tests.braid.f(X0, e2e_tests.braid.e()) = X0.
2: e2e_tests.braid.f(e2e_tests.braid.f(X0, X1), X2) = e2e_tests.braid.f(X0, e2e_tests.braid.f(X1, X2)).
3: e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.c1())) = e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c2())).
4: e2e_tests.braid.e() = e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c1()).
5: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.c2()) = e2e_tests.braid.e().
generated rules:
0: e2e_tests.braid.f(e2e_tests.braid.e(), X0) -> X0.
Proof: Axiom.

1: e2e_tests.braid.f(X0, e2e_tests.braid.e()) -> X0.
Proof: Axiom.

2: e2e_tests.braid.f(e2e_tests.braid.f(X0, X1), X2) -> e2e_tests.braid.f(X0, e2e_tests.braid.f(X1, X2)).
Proof: Axiom.

3: e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.c1())) <- e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c2())).
Proof: Axiom.

4: e2e_tests.braid.e() -> e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c1()).
Proof: Axiom.

5: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.c2()) -> e2e_tests.braid.e().
Proof: Axiom.

6: e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c1(), X0)) -> X0.
Proof: Rewrite equation 0,
- lhs by equation 4 L->R at [0]
- lhs by equation 2 L->R at []

7: e2e_tests.braid.f(X0, e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c1())) -> X0.
Proof: Rewrite equation 1,
- lhs by equation 4 L->R at [1]

8: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.c2()) -> e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c1()).
Proof: Rewrite equation 5,
- rhs by equation 4 L->R at []

9: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c2(), X2)) -> e2e_tests.braid.f(e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c1()), X2).
Proof: A critical pair between equations 2 and 8 with superposition e2e_tests.braid.f(e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.c2()), X2).

10: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c2()), X2)) <- e2e_tests.braid.f(e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.c1())), X2).
Proof: A critical pair between equations 2 and 3 with superposition e2e_tests.braid.f(e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c2())), X2).

11: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), X2))) -> e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), X2))).
Proof: Rewrite equation 10,
- lhs by equation 2 L->R at [1]
- rhs by equation 2 L->R at []
- rhs by equation 2 L->R at [1]

12: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c2(), X2)) -> X2.
Proof: Rewrite equation 9,
- rhs by equation 2 L->R at []
- rhs by equation 6 L->R at []

ES:
6: e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c1(), X0)) -> X0
7: e2e_tests.braid.f(X0, e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c1())) -> X0
2: e2e_tests.braid.f(e2e_tests.braid.f(X0, X1), X2) -> e2e_tests.braid.f(X0, e2e_tests.braid.f(X1, X2))
3: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c2())) -> e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.c1()))
4: e2e_tests.braid.e() -> e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c1())
8: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.c2()) -> e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.c1())
12: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c2(), X2)) -> X2
11: e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), X2))) -> e2e_tests.braid.f(e2e_tests.braid.c1(), e2e_tests.braid.f(e2e_tests.braid.c2(), e2e_tests.braid.f(e2e_tests.braid.c1(), X2)))


*)
