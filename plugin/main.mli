val prove_interreduce :
  name:Names.Id.t (* 証明する定理名 *)
  -> goal:Constrexpr.constr_expr (* 定理の型 *)
  -> rewriters:Libnames.qualid list
  -> applier:Libnames.qualid (* apply を行う定理名 *)
               -> unit

val complete : Libnames.qualid list -> string -> Libnames.qualid list -> Pp.t
