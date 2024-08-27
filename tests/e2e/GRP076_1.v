Declare ML Module "coq-completion.plugin".
(* Generated by tptp2coqp *)
Require Import Setoid.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter double_divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a1 : hint_hack_compl.
Axiom ax_identity : forall X : G, identity = (double_divide X (inverse X)).
Axiom ax_inverse : forall X : G, (inverse X) = (double_divide X identity).
Axiom ax_multiply : forall X Y : G, (multiply X Y) = (double_divide (double_divide Y X) identity).
Axiom ax_single_axiom : forall X Y Z : G, (double_divide (double_divide X (double_divide (double_divide (double_divide X Y) Z) (double_divide Y identity))) (double_divide identity identity)) = Z.

Complete ax_identity ax_inverse ax_multiply ax_single_axiom : a1 a2 a3 b3 c3 double_divide identity inverse multiply : hint
  for ((multiply (inverse a1) a1) = identity).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

