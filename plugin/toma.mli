(** Toma を利用するためのモジュール *)

(** 公理のリスト[Constr.t list] を与えて Toma を実行し、出力行のリスト[string list]を返す。 *)
val toma : Constr.t list -> string list

module V6 : sig
  val toma : Constr.t list -> string list
end