Declare ML Module "coq-completion.plugin".
Require Import Coq.Setoids.Setoid.

Parameter S : Set.
Parameter e : S.
Parameter f : S -> S.

Axiom ax : f e = e.

(* my_setoid_rewrite *)
Goal f e = e.
  my_setoid_rewrite ax.
  reflexivity.
Qed.

(* rewrite_pos *)
Goal f e = e.
  rewrite_pos -> ax at 1.
  reflexivity.
Qed.
Axiom ax_e_fe : f e = e.
Goal f e = f e.
  rewrite_pos -> ax at 2.
  apply ax_e_fe.
Qed.

Parameter f2 : S -> S -> S.
Parameter e2 : S.
Axiom ax2 : f2 e e = e2.
Goal f2 (f2 e e) (f2 (f2 e e) e) = f2 (f2 e e) (f2 e2 e).
  rewrite_pos lhs -> ax2 at 1 0.
  reflexivity.
Qed.

Axiom ax3 : forall X : S, f2 X X = e.
Goal e = e2.
  rewrite_pos lhs <- ax3.
  rewrite_pos rhs <- ax2.
  reflexivity.
Qed.
 
