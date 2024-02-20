open Names
open Constrexpr

(* List manipulations *)

(** 要素がリストに存在しない場合、新たに追加する *)
val insert_unique : 'a -> 'a list -> 'a list

(** 重複する要素がないように２つのリストを合併する *)
val merge : 'a list -> 'a list -> 'a list

(* string_of_* 系 *)
val string_of_lname : lname -> string
val string_of_binder_kind : binder_kind -> string
val string_of_local_binder_expr : local_binder_expr -> string
val string_of_constr_expr : constr_expr -> string