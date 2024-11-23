open Constr

module Term = struct
  type t = Var of string | App of string * t list

  let rec to_string = function
    | Var name -> name
    | App (f, args) ->
        String.concat ""
          [ f; " ("; String.concat ", " (List.map to_string args); ")" ]

  let rec fold_vars f init = function
    | Var name -> f init name
    | App (_, args) -> List.fold_left (fold_vars f) init args

  let mkVar name = Var name
  let mkApp f args = App (f, args)

  let rec of_constr ?varname_of_ind c =
    let of_constr = of_constr ?varname_of_ind in
    match kind c with
    | Rel i ->
        let varname =
          match varname_of_ind with
          | None -> "x" ^ string_of_int i
          | Some f -> f i
        in
        Var varname
    | App (f, args) ->
        let f : string =
          if isConst f then
            let k, _ = destConst f in
            Names.Constant.to_string k
          else raise (Invalid_argument "not implemented function type")
        in
        let args : t list = List.map of_constr (Array.to_list args) in
        mkApp f args
    | Const (k, _) -> mkVar (Names.Constant.to_string k)
    | Construct (((mutind, mutpos), pos), _) ->
      let prefix = Names.MutInd.to_string mutind |> String.split_on_char '.' |> List.rev |> List.tl |> List.rev |> String.concat "." in
      let cases = ComInductive.make_cases (mutind, mutpos) in
      let case = List.nth cases (pos - 1) in
      mkVar (prefix ^ "." ^ List.hd case)
    | Ind _ -> failwith "not implemented ind"
    | Var x -> Var (Names.Id.to_string x)
    | _ -> failwith "Term.of_constr: not implemented"

  let rec to_constr_expr t =
    let open Constrexpr in
    match t with
    | App (f, args) ->
        CAst.make
          (CApp
             ( CAst.make (CRef (Libnames.qualid_of_string f, None)),
               List.map (fun arg -> (to_constr_expr arg, None)) args ))
    | Var x -> CAst.make (CRef (Libnames.qualid_of_string x, None))
end

(* Equation := forall [varnames], left = right *)
type t = { left : Term.t; right : Term.t; varnames : string list }

let merge a b =
  let rec insert acc e =
    match acc with
    | [] -> [ e ]
    | hd :: tl as l -> if hd = e then l else hd :: insert tl e
  in
  List.fold_left insert a b

let left t = t.left
let right t = t.right
let varnames t = t.varnames

let varnames_in_term varnames term =
  let is_var name = List.exists (fun e -> e = name) varnames in
  let rec aux = function
    | Term.Var name -> if is_var name then [ name ] else []
    | App (_, args) -> List.fold_left merge [] (List.map aux args)
  in
  aux term

let varnames_in_left t = varnames_in_term t.varnames t.left
let varnames_in_right t = varnames_in_term t.varnames t.right

let to_string ?(with_prods = false) ?(arrow = `Eq) t =
  let prods =
    if with_prods then
      match t.varnames with
      | [] -> "(without variables) "
      | _ -> "forall " ^ String.concat " " t.varnames ^ ", "
    else ""
  in
  let sep = match arrow with `Eq -> " = " | `L2R -> " -> " | `R2L -> " <- " in
  let to_s = Term.to_string in
  prods ^ to_s t.left ^ sep ^ to_s t.right

let to_trs_string = to_string ~with_prods:false ~arrow:`L2R
let create ~varnames ~left ~right = { left; right; varnames }

let create_with_constants ~constants ~left ~right =
  let is_in ls v = List.exists (fun e -> e = v) ls in
  let is_const v = is_in constants v in
  let leftvars =
    Term.fold_vars
      (fun acc name ->
        if not (is_const name || is_in acc name) then name :: acc else acc)
      [] left
  in
  let varnames =
    Term.fold_vars
      (fun acc name ->
        if not (is_const name || is_in acc name) then name :: acc else acc)
      leftvars right
  in
  { left; right; varnames }

let variables_of_constr c =
  let rec aux acc c =
    if isProd c then
      let name, typ, subterm = destProd c in
      let binder_name = name.binder_name in
      match binder_name with
      | Anonymous -> aux acc subterm
      | Name id -> Names.Id.to_string id :: aux acc subterm
    else fold aux acc c
  in
  List.rev (aux [] c)

exception EarlyReturn of Constr.t option
(** Exception to early return.
    Intended to break fold, map or iter. *)

(** Finds App constructor of "=" recursively *)
let rec find_eq_opt c =
  let f_is_eq_p f =
    if not (isInd f) then false
    else
      let (mutind, _), _ = destInd f in
      "Coq.Init.Logic.eq" = Names.MutInd.to_string mutind
  in
  try
    match kind c with
    | App (f, _) when f_is_eq_p f -> Some c
    | _ ->
        iter
          (fun c ->
            match find_eq_opt c with
            | Some _ as v -> raise (EarlyReturn v)
            | None -> ())
          c;
        None
  with EarlyReturn v -> v

let of_constr c =
  let varnames = variables_of_constr c in
  let varname_of_ind i = List.nth varnames (i - 1) in
  match find_eq_opt c with
  | Some c ->
      let _, arr = destApp c in
      let left = Term.of_constr ~varname_of_ind arr.(1) in
      let right = Term.of_constr ~varname_of_ind arr.(2) in
      { varnames; left; right }
  | _ -> failwith "of_constr: invalid constr. argument c should contain '='."

let to_constr_expr t =
  let open Constrexpr in
  let ( <.> ) f g x = f (g x) in
  let vars =
    List.map
      (CAst.make <.> Names.Name.mk_name <.> Names.Id.of_string)
      t.varnames
  in
  let left = Term.to_constr_expr t.left in
  let right = Term.to_constr_expr t.right in
  CAst.make
    (CProdN
       ( [
           CLocalAssum
             ( vars,
               None,
               Default Explicit,
               CAst.make (CRef (Libnames.qualid_of_string (State.current_set_name ()), None)) );
         ],
         CAst.make
           (CApp
              ( CAst.make (CRef (Libnames.qualid_of_string "eq", None)),
                [ (left, None); (right, None) ] )) ))

let of_qualid id =
  let constant_body =
    match Nametab.global id with
    | ConstRef c -> Global.lookup_constant c
    | _ -> raise (Invalid_argument "qualid does not indicate constant")
  in
  let constr = constant_body.const_type in
  of_constr constr
