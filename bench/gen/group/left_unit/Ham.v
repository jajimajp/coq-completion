(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter e : G.
Parameter f : G -> G -> G.
Parameter i : G -> G.
Axiom associativity : forall X Y Z : G, (f (f X Y) Z) = (f X (f Y Z)).
Axiom right_inverse : forall X : G, (f X (i X)) = e.
Axiom right_unit : forall X : G, (f X e) = X.


(* Goal *)
Theorem check : forall X : G, (f e X) = X.
Proof.
  hammer.
Qed.

Check check.

