(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Parameter sk_c1 : G.
Parameter sk_c2 : G.
Parameter sk_c3 : G.
Parameter sk_c4 : G.
Parameter sk_c5 : G.
Parameter sk_c6 : G.
Parameter sk_c7 : G.
Parameter sk_c8 : G.
Axiom associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : G, (multiply identity X) = X.


(* Goal *)
Theorem check : (multiply sk_c6 sk_c8) = sk_c7.
Proof.
  hammer.
Qed.

Check check.

