(* Coq 上での操作 *)

val prove_by_axiom :
  name:Names.Id.t ->
  goal:Constrexpr.constr_expr ->
  axioms:Libnames.qualid list ->
  unit
(** 公理のうちのどれかから直ちに導ける規則を証明する
    公理の一つと同じか、両辺を入れ替えたものである必要がある。*)

val proof_using_crit :
  name:Names.variable ->
  n1:string ->
  n2:string ->
  l:My_term.term ->
  r:My_term.term ->
  crit:My_term.term ->
  constants:My_term.constants option ->
  unit

val prove_interreduce :
  name:Names.Id.t ->
  (* 証明する定理名 *)
  goal:Constrexpr.constr_expr ->
  (* 定理の型 *)
  rewriters:Libnames.qualid list ->
  applier:Libnames.qualid ->
  (* apply を行う定理名 *)
  unit

val tclPROVE_INTERREDUCE :
  name:Names.Id.t ->
  (* 証明する定理名 *)
  goal:Constrexpr.constr_expr ->
  (* 定理の型 *)
  rewriters:Libnames.qualid list ->
  applier:Libnames.qualid ->
  (* apply を行う定理名 *)
  unit

val tclSPECIALIZE_IF_NECESSARY : unit Proofview.tactic -> unit Proofview.tactic

val tclPRINT_GOAL : string -> unit Proofview.tactic
(** [tclPRINT_GOAL label] prints current goal with label. *)

val prove_completion_subject :
  name:Names.Id.t ->
  (* 証明する定理名 *)
  goal:Constrexpr.constr_expr ->
  (* 定理の型 *)
  rewriters:Libnames.qualid list ->
  unit
