open Names
open Constrexpr

(* string_of_* 系 *)
val string_of_lname : lname -> string
val string_of_binder_kind : binder_kind -> string
val string_of_local_binder_expr : local_binder_expr -> string
val string_of_constr_expr : constr_expr -> string