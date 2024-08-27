(**
  * 完備化プラグイン内で用いるための書換規則の表現
  * 等号を関数としてではなく特別に扱うなどの特徴がある
  *)

(* 書換規則 *)
type term = App of string * term list | Var of string
type t = term * term

val mkTermApp : string -> term list -> term
val mkVar : string -> term

(* 定数名の集合 *)
type constants

val empty_constants : constants
val default_constants : constants
val constants_of_list : string list -> constants
val list_of_constants : constants -> string list

(* 等しい term か *)
val eq_term : term -> term -> bool

(* 規則内の変数を返す *)
val variables : t -> string list

(* tomaで用いられるTRS表現の文字列との相互変換 *)
val from_trs : string -> t
val to_trs : t -> string
val variables_except_constants : t -> constants -> string list
val constrexpr_of_term : term -> Constrexpr.constr_expr
val to_constrexpr_raw : t -> constants -> Constrexpr.constr_expr
val of_constr : Constr.t -> t

(* Constr.tのリストをtのリストに変換したものと、定数（束縛されていないId）を返す *)
val parse_constrs : Constr.t list -> t list * constants
val pr : t -> Pp.t
