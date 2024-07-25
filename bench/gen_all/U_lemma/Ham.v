(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a : G -> G -> G.
Parameter i : G.
Parameter k : G.
Parameter s : G.
Parameter x : G.
Parameter y : G.
Axiom lem3 : (a (a (a s i) (a x x)) y) = (a (a i y) (a (a x x) y)).
Axiom lem2 : (a (a (a s i) i) x) = (a (a i x) (a i x)).
Axiom lem1 : (a (a (a s (a k (a s i))) (a (a s i) i)) x) = (a (a (a k (a s i)) x) (a (a (a s i) i) x)).
Axiom i_definition : forall X : G, (a i X) = X.
Axiom k_definition : forall X Y : G, (a (a k X) Y) = X.
Axiom s_definition : forall X Y Z : G, (a (a (a s X) Y) Z) = (a (a X Z) (a Y Z)).


(* Goal *)
Theorem check : (a (a (a (a s (a k (a s i))) (a (a s i) i)) x) y) = (a y (a (a x x) y)).
Proof.
  hammer.
Qed.

Check check.
