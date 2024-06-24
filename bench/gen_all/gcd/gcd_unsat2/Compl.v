(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter false : G.
Parameter gcd : G -> G -> G.
Parameter if_gcd : G -> G -> G -> G.
Parameter le : G -> G -> G.
Parameter minus : G -> G -> G.
Parameter s : G -> G.
Parameter true : G.
Parameter z : G.
Axiom if_gcd_false : forall X Y : G, (if_gcd false (s X) (s Y)) = (gcd (minus Y X) (s X)).
Axiom if_gcd_true : forall X Y : G, (if_gcd true (s X) (s Y)) = (gcd (minus X Y) (s Y)).
Axiom gcd_s_s : forall X Y : G, (gcd (s X) (s Y)) = (if_gcd (le Y X) (s X) (s Y)).
Axiom gcd_s_z : forall X : G, (gcd (s X) z) = (s X).
Axiom gcd_z : forall Y : G, (gcd z Y) = Y.
Axiom minus_s_s : forall X Y : G, (minus (s X) (s Y)) = (minus X Y).
Axiom minus_z : forall X : G, (minus X z) = X.
Axiom le_s_s : forall X Y : G, (le (s X) (s Y)) = (le X Y).
Axiom le_s_z : forall X : G, (le (s X) z) = false.
Axiom le_z : forall Y : G, (le z Y) = true.

Complete if_gcd_false if_gcd_true gcd_s_s gcd_s_z gcd_z minus_s_s minus_z le_s_s le_s_z le_z : false gcd if_gcd le minus s true z : hint
  for ((gcd (s z) (s z)) = (s z)).

(* Goal *)
Theorem check : (gcd (s z) (s z)) = (s z).
Proof.
  autorewrite with hint.
  reflexivity.
Qed.

Check check.

