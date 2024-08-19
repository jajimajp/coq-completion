(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom condition : forall X Y : G, (multiply X (multiply Y Y)) = (multiply Y (multiply Y X)).
Axiom associativity_of_multiply : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).


(* Goal *)
Theorem check : (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a b))))))) = (multiply a (multiply a (multiply a (multiply a (multiply b (multiply b (multiply b b))))))).
Proof.
  hammer.
Qed.

Check check.
