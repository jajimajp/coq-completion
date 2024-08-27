(** Equations, including terms *)

(** Term *)
module Term : sig
  type t

  val to_string : t -> string

  val mkVar : string -> t
  (** [mkVar name] creates variable with name [name]. *)

  val mkApp : string -> t list -> t
  (** [mkApp f [arg1; arg2; ...]] creates f (arg1, arg2, ...) *)

  val fold_vars : ('a -> string -> 'a) -> 'a -> t -> 'a

  val of_constr : ?varname_of_ind:(int -> string) -> Constr.t -> t
  (** Conversion from Constr.t
      Optional [varname_of_ind] is a converter from index into string.
      If [varname_of_ind] is not given, varnames will be x1, x2, .... *)

  val to_constr_expr : t -> Constrexpr.constr_expr
end

type t
(** Equation *)

val to_string : ?with_prods:bool -> ?arrow:[ `L2R | `R2L | `Eq ] -> t -> string
(** [to_string eq] returns string of equation [eq].
    {4 Examples}
    {[to_string eq]} <left> = <right>
    {[to_string ~with_prods:true eq]} forall x, <left> = <right>
    {[to_string ~arrow:`L2R eq]} <left> -> <right> *)

val to_trs_string : t -> string
(** [to_trs_string eq] returns string of [eq] in TRS form.
    Example: "e + x -> x" *)

val left : t -> Term.t
val right : t -> Term.t
val varnames : t -> string list
val varnames_in_left : t -> string list
val varnames_in_right : t -> string list

val create : varnames:string list -> left:Term.t -> right:Term.t -> t
(** Creates equation.
    {4 Examples}
    [create ~varnames:["x"] ~left ~right] represents
      forall x, left = right. *)

val create_with_constants :
  constants:string list -> left:Term.t -> right:Term.t -> t
(** Creates equation using constants:
      if Var is in constants, it is not variable (= not appear in <forall foo bar ...,>)
    {4 Examples}
    [create ~varnames:["x"] ~left ~right] represents
      forall x, left = right. *)

(* Conversion from Constr.t *)
val of_constr : Constr.t -> t
val to_constr_expr : t -> Constrexpr.constr_expr

val of_qualid : Libnames.qualid -> t
(** Make t from Constr indicated by qualid *)
