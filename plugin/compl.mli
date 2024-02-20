(** Manage completion algorithm state *)

val complete :
  axioms:Libnames.qualid list ->
  constants:Libnames.qualid list ->
  hint_db_name:string ->
  Pp.t
