open Names
open Constrexpr

(* List manipulations *)

(** 全てtrueのリストから始めて、2^n 個の組み合わせを試すための次のリストを返す
    全ての要素がfalseの場合（列挙終了時）はNoneを返す
    *)
val next_binls : bool list -> bool list option

(** 要素がリストに存在しない場合、新たに追加する *)
val insert_unique : 'a -> 'a list -> 'a list

(** 重複する要素がないように２つのリストを合併する *)
val merge : 'a list -> 'a list -> 'a list

(* string_of_* 系 *)
val string_of_lname : lname -> string
val string_of_binder_kind : binder_kind -> string
val string_of_local_binder_expr : local_binder_expr -> string
val string_of_constr_expr : constr_expr -> string