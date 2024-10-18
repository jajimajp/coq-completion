(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a2 : G.
Parameter b2 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a2.
Axiom ax_single_axiom : forall A B C D : G, (inverse (multiply (multiply (multiply (inverse (multiply (multiply A B) C)) A) B) (multiply D (inverse D)))) = C.

Complete ax_single_axiom : a2 b2 inverse multiply : hint
  for ((multiply (multiply (inverse b2) b2) a2) = a2).

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

