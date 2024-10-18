(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter identity : G.
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
Hint Resolve identity.
Axiom ax_prove_this_1 : (multiply sk_c7 sk_c8) = sk_c6.
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.

Complete ax_prove_this_1 ax_associativity ax_left_inverse ax_left_identity : identity inverse multiply sk_c1 sk_c2 sk_c3 sk_c4 sk_c5 sk_c6 sk_c7 sk_c8 : hint
  for ((multiply sk_c1 sk_c7) = sk_c8).

(* Goal *)
Theorem check : (multiply sk_c1 sk_c7) = sk_c8.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

