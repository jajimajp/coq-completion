open Names
module SS = Set.Make (String)

type term = App of string * term list | Var of string

(* (左辺, 右辺)で等式を表現する *)
type t = term * term

let mkTermApp f args = App (f, args)
let mkVar x = Var x

let rec eq_term t1 t2 =
  match (t1, t2) with
  | App (f1, args1), App (f2, args2) ->
      f1 = f2 && List.for_all2 eq_term args1 args2
  | Var x1, Var x2 -> x1 = x2
  | _ -> false

type constants = SS.t

let empty_constants = SS.empty

let default_constants_list =
  [
    "eq";
    "e";
    "G";
    "f";
    "AutoEqProver.Test.e";
    "AutoEqProver.Test.f";
    "Test.e";
    "Test.f";
  ]
(* TODO *)

let set_of_list ls =
  let rec aux acc = function [] -> acc | hd :: tl -> aux (SS.add hd acc) tl in
  aux SS.empty ls

let default_constants = set_of_list default_constants_list
let constants_of_list = set_of_list
let list_of_constants = SS.elements

let variables t =
  let t1, t2 = t in
  let rec variables_set = function
    | App (f, args) ->
        let args = List.map variables_set args in
        List.fold_left SS.union SS.empty args
    | Var x -> SS.add x SS.empty
  in
  let ids = SS.union (variables_set t1) (variables_set t2) in
  SS.elements ids

let variables_except_constants t constants =
  let vs = set_of_list (variables t) in
  SS.elements (SS.diff vs constants)

(* トップレベルのカンマで区切る *)
let split_by_comma s =
  let chars = List.of_seq (String.to_seq s) in
  let rec loop acc l level =
    match l with
    | [] -> [ acc ] (* TODO: 現在0~1個のカンマ直後のスペースにしか対応していない *)
    | ',' :: ' ' :: t | ',' :: t ->
        if level = 0 then acc :: loop [] t level
        else loop (acc @ [ ',' ]) t level
    | '(' :: t -> loop (acc @ [ '(' ]) t (level + 1)
    | ')' :: t -> loop (acc @ [ ')' ]) t (level - 1)
    | h :: t -> loop (acc @ [ h ]) t level
  in
  let string_of_chars l = String.of_seq (List.to_seq l) in
  List.map string_of_chars (loop [] chars 0)

let rec term_of_string str =
  let reg = Str.regexp "^\\([^(]+\\)(\\(.+\\))$" in
  match Str.string_match reg str 0 with
  | true ->
      let f = Str.matched_group 1 str in
      let args_str = Str.matched_group 2 str in
      let args_str_list = split_by_comma args_str in
      let args = List.map term_of_string args_str_list in
      App (f, args)
  | false -> Var str

let from_trs s =
  match Str.split (Str.regexp " -> ") s with
  (* １つの等号がある等式しかサポートしない *)
  | [ t1; t2 ] ->
      let t1 = term_of_string t1 in
      let t2 = term_of_string t2 in
      (t1, t2)
  | _ -> failwith ("Invalid input of TRS string: " ^ s)

let rec trs_string_of_term = function
  | App (f, args) ->
      let args = String.concat ", " (List.map trs_string_of_term args) in
      f ^ "(" ^ args ^ ")"
  | Var x -> x

let to_trs t =
  let t1, t2 = t in
  trs_string_of_term t1 ^ " -> " ^ trs_string_of_term t2

let rec constrexpr_of_term t =
  let open Constrexpr in
  match t with
  | App (f, args) ->
      let args_constr =
        List.map (fun arg -> (constrexpr_of_term arg, None)) args
      in
      CAst.make
        (CApp (CAst.make (CRef (Libnames.qualid_of_string f, None)), args_constr))
  | Var x -> CAst.make (CRef (Libnames.qualid_of_string x, None))

(* without proof using force_admit *)
let to_constrexpr_raw (t1, t2) constants =
  let open Constrexpr in
  let vars = variables_except_constants (t1, t2) constants in
  let t1 = constrexpr_of_term t1 in
  let t2 = constrexpr_of_term t2 in
  CAst.make
    (CProdN
       ( [
           CLocalAssum
             ( List.map
                 (fun name ->
                   CAst.make (Names.Name.mk_name (Id.of_string name)))
                 vars,
               None,
               Default Explicit,
               CAst.make (CRef (Libnames.qualid_of_string "G", None)) );
         ],
         CAst.make
           (CApp
              ( CAst.make (CRef (Libnames.qualid_of_string "eq", None)),
                [ (t1, None); (t2, None) ] )) ))

open Constr

type term_or_eq = Term of term | Eq of term * term

let of_constr (c : Constr.t) =
  let rec aux = function
    | Rel i -> Term (Var ("x" ^ string_of_int i))
    | Prod (_, _, t) -> aux (Constr.kind t)
    | App (f, args) -> (
        (* f が "=" であるか *)
        let is_eq constr =
          match Constr.kind constr with
          | Ind (ind, _) ->
              let mutind, i = ind in
              let smut = Names.MutInd.to_string mutind in
              smut = "Coq.Init.Logic.eq"
          | _ -> false
        in
        let args_t =
          List.map
            (fun t ->
              match aux (Constr.kind t) with
              | Term t -> t
              | _ ->
                  failwith "Invalid input: my_term.from_constr.case App args_t")
            (Array.to_list args)
        in
        if is_eq f then
          let errs = String.concat " , " (List.map trs_string_of_term args_t) in
          match args_t with
          | _ :: arg1 :: arg2 :: _ -> Eq (arg1, arg2)
          | _ ->
              failwith
                ("Invalid input: my_term.from_constr.case App is_eq" ^ errs)
        else
          match aux (Constr.kind f) with
          | Term (Var f_name) ->
              let args_list = args_t in
              Term (App (f_name, args_list))
          | _ -> failwith "Invalid input: match aux")
    | Const (k, _) -> Term (Var (Names.Constant.to_string k))
    (* for LPO *)
    | Var x -> Term (Var (Id.to_string x))
    | c ->
        let pr_label = function
          | Rel i -> "Rel " ^ string_of_int i
          | Var x -> "Var " ^ Id.to_string x
          | Meta _ -> "Meta"
          | Evar _ -> "Evar"
          | Sort _ -> "Sort"
          | Cast (_, _, _) -> "Cast"
          | Prod (_, _, _) -> "Prod"
          | Lambda (_, _, _) -> "Lambda"
          | LetIn (_, _, _, _) -> "LetIn"
          | App (_, _) -> "App"
          | Const (_, _) -> "Const"
          | Ind (_, _) -> "Ind"
          | Construct (_, _) -> "Construct"
          | Case (_, _, _, _, _, _, _) -> "Case"
          | Fix _ -> "Fix"
          | CoFix _ -> "CoFix"
          | Proj (_, _, _) -> "Proj"
          | Int _ -> "Int"
          | Float _ -> "Float"
          | Array _ -> "Array"
          | String _ -> "String"
        in
        failwith ("Not implemented" ^ pr_label c)
  in
  match aux (Constr.kind c) with
  | Eq (t1, t2) -> (t1, t2)
  | _ -> failwith "Invalid input: not Eq"

let constants_of_constr e =
  let rec aux = function
    | Rel i -> SS.empty
    | Prod (_, _, t) -> aux (Constr.kind t)
    | App (f, args) ->
        let args_constants =
          List.map (fun x -> aux (Constr.kind x)) (Array.to_list args)
        in
        List.fold_left (fun a b -> SS.union a b) SS.empty args_constants
    | Const (k, _) -> SS.singleton (Names.Constant.to_string k)
    | _ -> failwith "Not implemented"
  in
  aux (Constr.kind e)

let parse_constrs l =
  let ts = List.map of_constr l in
  let constant_list = List.map constants_of_constr l in
  let constants = List.fold_left SS.union SS.empty constant_list in
  (ts, constants)

let pr t =
  let open Pp in
  str (to_trs t)
