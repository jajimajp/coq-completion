Require Import Coq.Setoids.Setoid.
(* From Completion Require Import Plugin. *)

(* 集合 *)
Parameter G : Set.
(* + *)
Parameter f : G -> G -> G.
Infix "+" := f (at level 50, left associativity).
(* 単位元 *)
Parameter e : G.
(* - *)
Parameter i : G -> G.

(**** 公理 ****)
(* 結合律 *)
Axiom assoc : forall a b c, a + b + c = a + (b + c).
(* 左単位元 *)
Axiom id_l : forall a, e + a = a.
(* 左逆元 *)
Axiom inv_l : forall a, i a + a = e.
(* 可換 *)
Axiom comm : forall a b, a + b = b + a.

Theorem check : forall x y, y + (x + x) = x + (x + y).
  Proof.
    assert (H0 : forall x0 x1 x2, (x0 + x1) + x2 = x0 + (x1 + x2)) by (
               apply assoc).
    assert (H3 : forall x0 x1, (x0 + x1) = (x1 + x0)) by (
               apply comm).
    assert (H9 : forall x3 x4 x5, x5 + (x3 + x4) = x3 + (x4 + x5)) by
    (
      assert (H_0 : forall x3 x4 x5, (x3 + x4) + x5 = x5 + (x3 + x4)) by
      (
        idtac "a";
        intros;
        setoid_rewrite (* H3 *) comm at 1;
        reflexivity
      );
      assert (H_1 : forall x3 x4 x5, (x3 + x4) + x5 = x3 + (x4 + x5)) by
      (
        intros;
        setoid_rewrite H0 at 1;
        reflexivity
      );
      intros;
      rewrite <- H_0;
      rewrite H_1;
      reflexivity
    ).
    Check comm.

Theorem check1: forall x y, y + (x + x) = x + (x + y).
Proof.
  by_complete assoc id_l inv_l comm : f e i.
  assert (H : forall x y, x + (x + y) = y + (x + x)).
  {
    setoid_rewrite H3 at 2.
    setoid_rewrite H0.
  }


Qed.

Print check1.
