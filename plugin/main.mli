val prove_interreduce :
  name:Names.Id.t (* 証明する定理名 *)
  -> goal:Constrexpr.constr_expr (* 定理の型 *)
  -> rewriters:Libnames.qualid list
  -> applier:Libnames.qualid (* apply を行う定理名 *)
               -> unit

val complete : Libnames.qualid list -> string -> Libnames.qualid list -> Pp.t

val complete_for : Constrexpr.constr_expr -> Libnames.qualid list -> string -> Libnames.qualid list -> Pp.t

val complete_in_tac :
  string list    (* 公理名一覧 *)
  -> string list (* 定数名一覧 *)
  -> Locus.clause
  -> unit Proofview.tactic

(** [lpo_autorewrite_with hintDb] returns tactic to rewrite current goal term. *)
val lpo_autorewrite_with : string -> Locus.clause -> unit Proofview.tactic