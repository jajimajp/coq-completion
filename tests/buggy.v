Require Import Coq.Setoids.Setoid.

Variable S : Set.

Variable nil : S.
Variable cons : S -> S -> S.
Variable append : S -> S -> S.
Variable ifappend : S -> S -> S -> S.

Axiom th0 : forall x7 x3 x4 x2 x9,
    ifappend x2 x3 (ifappend x7 x9 (cons x4 nil)) = cons x4 (ifappend (ifappend nil x9 nil) x3 x9).
Axiom th1 : forall x0 x2 x5, ifappend x2 x5 (cons x0 nil) = cons x0 x5.
Axiom th2 : forall x2 x3, ifappend x2 x3 x2 = append x2 x3.

(* Not working *)
Goal forall x2 x3 x4 x9 : S, ifappend x2 x3 (cons x4 x9) = cons x4 (ifappend (append nil x9) x3 x9).
  Proof.
    intros.
    pose proof th0.
    setoid_rewrite th1 in H.
    setoid_rewrite th2 in H.
    specialize H with (1:=x2).
    apply H.
  Qed.


Axiom t80 : forall x0 x14 x15 x16 x17 x18 x19 : S,
    ifappend x0 x14 (cons x16 (ifappend x17 x18 x17))
    = ifappend x15 x14 (ifappend x19 x18 (cons x16 x17)).

Axiom t2 : forall x0 x1 : S, ifappend x0 x1 x0 = append x0 x1.
Axiom t86 : forall x5 x6 x7 : S,
      append (cons x6 x7) x5 = cons x6 (append x7 x5).
Axiom t88 : forall x0 x14 x15 x16 x17 x18 x19 : S,
  ifappend x15 x14 (append (cons x16 x17) x18)
  = ifappend x0 x14 (ifappend x19 x18 (cons x16 x17)).

Theorem t89 : forall x0 x14 x15 x16 x17 x18 : S,
    ifappend x0 x14 (append (cons x16 x17) x18)
    = ifappend x15 x14 (append (cons x16 x17) x18).
  Proof.
    intros.
    pose proof t80.
    setoid_rewrite t2 in H.
    setoid_rewrite <- t86 in H.
    setoid_rewrite <- t88 in H.
    instantiate (1:=x15) in H.
    specialize H with (1:=nil) (2:=nil).
    apply H.
  Qed.

Print t89.
