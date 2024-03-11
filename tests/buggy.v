Require Import Coq.Setoids.Setoid.

Variable S : Set.

Variable nil : S.
Variable cons : S -> S -> S.
Variable append : S -> S -> S.
Variable ifappend : S -> S -> S -> S.

Axiom th0 : forall x2 x3 x4 x7 x9,
    ifappend x2 x3 (ifappend x7 x9 (cons x4 nil)) = cons x4 (ifappend (ifappend nil x9 nil) x3 x9).
Axiom th1 : forall x0 x2 x5, ifappend x2 x5 (cons x0 nil) = cons x0 x5.
Axiom th2 : forall x2 x3, ifappend x2 x3 x2 = append x2 x3.

(* Not working *)
Goal forall x2 x3 x4 x9 : S, ifappend x2 x3 (cons x4 x9) = cons x4 (ifappend (append nil x9) x3 x9).
  Proof.
    pose proof th0.
    setoid_rewrite th1 in H.
    setoid_rewrite th2 in H.
    Abort.
    (* apply H. *) (* <- Error: Unable to Unify *)
  (* Qed *)
