(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a3 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a3.
Axiom ax_single_axiom : forall A B C D : G, (inverse (multiply (multiply (multiply (inverse (multiply (multiply A B) C)) A) B) (multiply D (inverse D)))) = C.

Complete ax_single_axiom : a3 b3 c3 inverse multiply : hint
  for ((multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3))).

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

