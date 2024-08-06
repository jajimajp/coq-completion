(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom single_axiom : forall A B C D : G, (multiply A (inverse (multiply (multiply (inverse (multiply (inverse B) (multiply (inverse A) C))) D) (inverse (multiply B D))))) = C.

Complete single_axiom : inverse multiply : hint
  for ((multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3))).

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

