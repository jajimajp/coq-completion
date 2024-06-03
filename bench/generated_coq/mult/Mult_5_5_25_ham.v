Require Import Setoid.
From Hammer Require Import Hammer.

(* Axioms *)
Parameter G : Set.
Parameter z : G.
Parameter s : G -> G.
Parameter add : G -> G -> G.
Parameter mult : G -> G -> G.
Axiom add_z : forall Y : G, add z Y = Y.
Axiom add_s : forall X Y : G, add (s X) Y = s (add X Y).
Axiom mult_z : forall Y : G, mult z Y = z.
Axiom mult_s : forall X Y : G, mult (s X) Y = add (mult X Y) Y.

Theorem check : (mult (s (s (s (s (s z))))) (s (s (s (s (s z)))))
  =
  (s (s (s (s (s (s (s (s (s (s
  (s (s (s (s (s (s (s (s (s (s
  (s (s (s (s (s
  z)))))))))))))))))))))))))).
Proof.
  hammer.
Qed.

Check check.
