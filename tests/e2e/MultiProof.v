Declare ML Module "coq-completion.plugin".
Require Import Coq.Setoids.Setoid.

Parameter G : Set.
Parameter f : G -> G -> G.
Parameter e : G.
Parameter i : G -> G.

Axiom assoc : forall a b c, f (f a b) c = f a (f b c).
Axiom id_l : forall a, f e a = a.
Axiom inv_l : forall a, f (i a) a = e.

Complete assoc id_l inv_l : f e i : hint_compl.

Theorem check1: forall x y, f (i x) (f x y) = y.
Proof.
  intros.
  lpo_autorewrite with hint_compl.
  reflexivity.
Qed.

Check check1.


(* Next proof *)

Parameter S : Set.
Parameter f2 : S -> S -> S.
Infix "+" := f2 (at level 50, left associativity).
Parameter e2 : S.
Parameter i2 : S -> S.

Axiom assoc2 : forall a b c, a + b + c = a + (b + c).
Axiom id_l2 : forall a, e2 + a = a.
Axiom inv_l2 : forall a, i2 a + a = e2.
Axiom comm2 : forall a b, a + b = b + a.


Complete assoc2 id_l2 inv_l2 comm2 : f2 e2 i2 : hint2 for (forall x y, x + (i2 x + y) = y).

Theorem check2 : forall x y, x + (i2 x + y) = y.
Proof.
  lpo_autorewrite with hint2.
  reflexivity.
Qed.

Check check2.
