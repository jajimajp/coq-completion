(* tomaを利用するためのモジュール *)

(* toma の出力を返す *)
val execute_toma : My_term.t list -> string list

val toma : Constr.t list -> string list -> string list