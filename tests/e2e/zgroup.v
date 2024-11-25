Declare ML Module "coq-completion.plugin".
(* From Completion Require Import Plugin. *)

Require Import Coq.Setoids.Setoid.

(* 集合 *)
Parameter G : Set.
(* + *)
Parameter f : G -> G -> G.
Infix "+" := f (at level 50, left associativity).
(* 単位元 *)
Parameter e : G.
(* - *)
Parameter i : G -> G.

(**** 公理 ****)
(* 結合律 *)
Axiom assoc : forall a b c : G, a + (b + c) = a + b + c.
(* 左単位元 *)
Axiom id_l : forall a : G, e + a = a.
(* 左逆元 *)
Axiom inv_l : forall a : G, i a + a = e.

Structure Group A := mkGroup
  { E     : A
  ; I     : A -> A
  ; F     : A -> A -> A
  ; Ident : forall a, F E a = a
  ; Inv   : forall a, F (I a) a = E
  ; Assoc : forall a b c, F a (F b c) = F (F a b) c
  }.

Require Import ZAxioms ZProperties BinInt.
Local Open Scope Z_scope.

Definition ZG :=
  {| Ident := Z.add_0_l
   ; Inv   := Z.add_opp_diag_l
   ; Assoc := Z.add_assoc
   |}.


Complete Record ZG : my_hint.

Print Rewrite HintDb my_hint.
(* 
Theorem check : forall a, f a e = a.
  intros. lpo_autorewrite with my_hint. reflexivity. Qed.

Check check.
*)
