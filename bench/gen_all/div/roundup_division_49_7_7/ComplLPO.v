(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter div : G -> G -> G.
Parameter minus : G -> G -> G.
Parameter s : G -> G.
Parameter z : G.
Axiom div_s : forall X Y : G, (div (s X) (s Y)) = (s (div (minus X Y) (s Y))).
Axiom div_z : forall Y : G, (div z (s Y)) = z.
Axiom minus_s : forall X Y : G, (minus (s X) (s Y)) = (minus X Y).
Axiom minus_z_right : forall X : G, (minus X z) = X.
Axiom minus_z_left : forall Y : G, (minus z Y) = z.

Complete div_s div_z minus_s minus_z_right minus_z_left : div minus s z : hint
  for ((div (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z))))))))))))))))))))))))))))))))))))))))))))))))) (s (s (s (s (s (s (s z)))))))) = (s (s (s (s (s (s (s z)))))))).

(* Goal *)
Theorem check : (div (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z))))))))))))))))))))))))))))))))))))))))))))))))) (s (s (s (s (s (s (s z)))))))) = (s (s (s (s (s (s (s z))))))).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

