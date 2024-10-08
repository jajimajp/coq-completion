(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter identity : G.
Parameter intersection : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Parameter negative_part : G -> G.
Parameter positive_part : G -> G.
Parameter union : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a : hint_hack_compl.
Axiom ax_negative_part : forall X : G, (negative_part X) = (intersection X identity).
Axiom ax_positive_part : forall X : G, (positive_part X) = (union X identity).
Axiom ax_multiply_intersection2 : forall X Y Z : G, (multiply (intersection Y Z) X) = (intersection (multiply Y X) (multiply Z X)).
Axiom ax_multiply_union2 : forall X Y Z : G, (multiply (union Y Z) X) = (union (multiply Y X) (multiply Z X)).
Axiom ax_multiply_intersection1 : forall X Y Z : G, (multiply X (intersection Y Z)) = (intersection (multiply X Y) (multiply X Z)).
Axiom ax_multiply_union1 : forall X Y Z : G, (multiply X (union Y Z)) = (union (multiply X Y) (multiply X Z)).
Axiom ax_intersection_union_absorbtion : forall X Y : G, (intersection (union X Y) Y) = Y.
Axiom ax_union_intersection_absorbtion : forall X Y : G, (union (intersection X Y) Y) = Y.
Axiom ax_union_associative : forall X Y Z : G, (union X (union Y Z)) = (union (union X Y) Z).
Axiom ax_intersection_associative : forall X Y Z : G, (intersection X (intersection Y Z)) = (intersection (intersection X Y) Z).
Axiom ax_union_commutative : forall X Y : G, (union X Y) = (union Y X).
Axiom ax_intersection_commutative : forall X Y : G, (intersection X Y) = (intersection Y X).
Axiom ax_union_idempotent : forall X : G, (union X X) = X.
Axiom ax_intersection_idempotent : forall X : G, (intersection X X) = X.
Axiom ax_inverse_product_lemma : forall X Y : G, (inverse (multiply X Y)) = (multiply (inverse Y) (inverse X)).
Axiom ax_inverse_involution : forall X : G, (inverse (inverse X)) = X.
Axiom ax_inverse_of_identity : (inverse identity) = identity.
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.

Complete ax_negative_part ax_positive_part ax_multiply_intersection2 ax_multiply_union2 ax_multiply_intersection1 ax_multiply_union1 ax_intersection_union_absorbtion ax_union_intersection_absorbtion ax_union_associative ax_intersection_associative ax_union_commutative ax_intersection_commutative ax_union_idempotent ax_intersection_idempotent ax_inverse_product_lemma ax_inverse_involution ax_inverse_of_identity ax_associativity ax_left_inverse ax_left_identity : a identity intersection inverse multiply negative_part positive_part union : hint
  for ((multiply (positive_part a) (negative_part a)) = a).

(* Goal *)
Theorem check : (multiply (positive_part a) (negative_part a)) = a.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

