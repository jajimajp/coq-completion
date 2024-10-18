(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a3 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Hint Resolve a3.
Axiom ax_multiply : forall A B : G, (multiply A B) = (inverse (double_divide B A)).
Axiom ax_single_axiom : forall A B C D : G, (double_divide (double_divide A (inverse (double_divide B C))) (double_divide (inverse B) (inverse (double_divide D (double_divide A D))))) = C.

Complete ax_multiply ax_single_axiom : a3 b3 c3 double_divide inverse multiply : hint
  for ((multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3))).

(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

