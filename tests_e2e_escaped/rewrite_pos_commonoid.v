(* Prove commonoid example with rewrite_pos *)
Require Import Coq.Setoids.Setoid.

Declare ML Module "coq-completion.plugin".
(* From Completion Require Import Plugin. *)

Parameter S : Set.
Parameter e : S.
Parameter f : S -> S -> S.

(*
Completed
order:
LPO with precedence: commonoid.e > commonoid.f > ___false > ___true
axioms:
0: commonoid.f(X0, X1) = commonoid.f(X1, X0).
1: commonoid.f(commonoid.e(), X0) = X0.
2: commonoid.f(commonoid.f(X0, X1), X2) = commonoid.f(X0, commonoid.f(X1, X2)).
*)

Axiom a0 : forall X0 X1, f X0 X1 = f X1 X0.
Axiom a1 : forall X0, f e X0 = X0.
Axiom a2 : forall X0 X1 X2, f (f X0 X1) X2 = f X0 (f X1 X2).

(*
generated rules:
0: commonoid.f(X0, X1) = commonoid.f(X1, X0).
Proof: Axiom.
*)
Theorem t0 : forall X0 X1, f X0 X1 = f X1 X0.
  apply a0. Qed.

(* 1: commonoid.f(commonoid.e(), X0) -> X0.
   Proof: Axiom. *)
Theorem t1 : forall X0, f e X0 = X0.
  apply a1. Qed.

(* 2: commonoid.f(commonoid.f(X0, X1), X2) -> commonoid.f(X0, commonoid.f(X1, X2)).
   Proof: Axiom. *)
Theorem t2 : forall X0 X1 X2, f (f X0 X1) X2 = f X0 (f X1 X2).
  apply a2. Qed.

(* 3: commonoid.f(X2, commonoid.e()) -> X2.
   Proof: A critical pair between equations 0 and 1 with superposition commonoid.f(commonoid.e(), X2). *)
Theorem t3 : forall X2, f X2 e = X2.
  intros.
  assert (f X2 e = f e X2). {
    apply t0.
  }
  assert (X2 = f e X2). {
    rewrite_pos rhs a1. reflexivity.
  }
  rewrite_pos lhs H.
  rewrite_pos rhs H0.
  reflexivity.
Qed.

(* 4: commonoid.f(X5, commonoid.f(X3, X4)) = commonoid.f(X3, commonoid.f(X4, X5)).
Proof: A critical pair between equations 0 and 2 with superposition commonoid.f(commonoid.f(X3, X4), X5).
*)
Theorem t4 : forall X3 X4 X5, f X5 (f X3 X4) = f X3 (f X4 X5).
  intros.
  assert (f X5 (f X3 X4) = f (f X3 X4) X5). {
    rewrite_pos lhs t0. reflexivity.
  }
  assert (f X3 (f X4 X5) = f (f X3 X4) X5). {
    rewrite_pos lhs <- t2. reflexivity.
  }
  rewrite_pos lhs H.
  rewrite_pos rhs H0.
  reflexivity.
Qed.


(* 5: commonoid.f(X3, commonoid.f(X4, X2)) <- commonoid.f(commonoid.f(X4, X3), X2).
Proof: A critical pair between equations 2 and 0 with superposition commonoid.f(commonoid.f(X3, X4), X2).
*)
Theorem t5 : forall X2 X3 X4, f X3 (f X4 X2) = f (f X4 X3) X2.
  intros.
  assert (f X3 (f X4 X2) = f (f X3 X4) X2). {
    rewrite_pos lhs <- t2. reflexivity.
  }
  assert (f (f X4 X3) X2 = f (f X3 X4) X2). {
    rewrite_pos lhs t0 at 0. reflexivity.
  }
  rewrite_pos lhs H.
  rewrite_pos rhs H0.
  reflexivity.
Qed.


(*
6: commonoid.f(X3, commonoid.f(X4, X2)) = commonoid.f(X4, commonoid.f(X3, X2)).
Proof: Rewrite equation 5,
=> equation 2, rhs at [] *)
Theorem t6 : forall X2 X3 X4, f X3 (f X4 X2) = f X4 (f X3 X2).
  pose proof t5.
  rewrite_pos rhs t2 in H.
  apply H.
Qed.

(*
ES:
1: commonoid.f(commonoid.e(), X0) -> X0
2: commonoid.f(commonoid.f(X0, X1), X2) -> commonoid.f(X0, commonoid.f(X1, X2))
3: commonoid.f(X2, commonoid.e()) -> X2
0: commonoid.f(X0, X1) = commonoid.f(X1, X0)
4: commonoid.f(X5, commonoid.f(X3, X4)) = commonoid.f(X3, commonoid.f(X4, X5))
6: commonoid.f(X3, commonoid.f(X4, X2)) = commonoid.f(X4, commonoid.f(X3, X2))
*)
