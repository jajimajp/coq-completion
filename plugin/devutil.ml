open Constrexpr

(** 全てtrueから始めて、2^n 個の組み合わせを試すための次のリストを返す *)
let next_binls ls =
  let r = List.rev ls in
  let rec find_tru_idx i = function
  | [] -> None
  | true :: _ -> Some i
  | false :: rest -> find_tru_idx (i + 1) rest in
  let true_idx = find_tru_idx 0 r in
  (* nthの要素をfalseに、それ以前の要素を全てtrueにしたリスト *)
  let rec toggle nth i = function
  | [] -> []
  | (hd :: tl) as l ->
    if i = nth then false :: tl
    else if i < nth then true :: toggle nth (i + 1) tl
    else l in
  match true_idx with
  | None -> None
  | Some i -> Some (List.rev (toggle i 0 r))


let insert_unique x l =
  if List.mem x l then l else x :: l

let merge l1 l2 =
  List.fold_left (fun acc x -> insert_unique x acc) l1 l2

let string_of_lname lname =
  lname.CAst.v
  |> Names.Name.print
  |> Pp.string_of_ppcmds

let string_of_binder_kind = function
| Default bk -> Printf.sprintf "Default (%s)" (
  match bk with
  | Explicit -> "Explicit"
  | MaxImplicit -> "MaxImplicit"
  | NonMaxImplicit -> "NonMaxImplicit"
)
| Generalized _ -> "<TODO Generalized>"

let string_of_constr_expr_label t =
  match t.CAst.v with
  | CRef _ -> "CRef"
  | CFix _ -> "CFix"
  | CCoFix _ -> "CCoFix"
  | CProdN _ -> "CProdN"
  | CAppExpl _ -> "CAppExpl"
  | CApp _ -> "CApp"
  | CProj _ -> "CProj"
  | CLambdaN _ -> "CLambdaN"
  | CLetIn _ -> "CLetIn"
  | CRecord _ -> "CRecord"
  | CCases _ -> "CCases"
  | CLetTuple _ -> "CLetTuple"
  | CIf _ -> "CIf"
  | CHole _ -> "CHole"
  | CPatVar _ -> "CPatVar"
  | CEvar _ -> "CEvar"
  | CSort _ -> "CSort"
  | CCast _ -> "CCast"
  | CNotation _ -> "CNotation"
  | CGeneralization _ -> "CGeneralization"
  | CPrim _ -> "CPrim"
  | CDelimiters _ -> "CDelimiters"
  | CArray _ -> "CArray"
  | _ -> "<Not implemented>"

let rec string_of_local_binder_expr = function
| CLocalAssum (ls, bk, ce) ->
  Printf.sprintf "CLocalAssum ((%s), %s, %s)"
    (String.concat "," (List.map string_of_lname ls))
    (string_of_binder_kind bk)
    (string_of_constr_expr ce)
| CLocalDef (ln, ce, None) ->
  Printf.sprintf "CLocalDef (%s, %s, None)"
    (string_of_lname ln)
    (string_of_constr_expr ce)
| CLocalDef (ln, ce, Some ceo) ->
  Printf.sprintf "CLocalDef (%s, %s, Some (%s))"
    (string_of_lname ln)
    (string_of_constr_expr ce)
    (string_of_constr_expr ceo)
| CLocalPattern _ -> "<TODO CLocalPattern>"

and string_of_local_binder_expr_list ls =
  let inside = ls
    |> List.map string_of_local_binder_expr
    |> String.concat "," in
  "local_binder (" ^ inside ^ ")"

and string_of_constr_expr (e : Constrexpr.constr_expr) : string =
  let rec string_of_constrexpr_r = function
  | CRef (qid, opt) ->
    let opts = (match opt with None -> "None" | Some a -> "Some <todo>") in
    "CRef (" ^ (Libnames.string_of_qualid qid) ^ ", " ^ opts ^ ")"
  | CApp (c, l) ->
    let cs = string_of_constrexpr_r c.v in
    let ls = List.map (fun (i, _) -> string_of_constrexpr_r i.CAst.v) l in
    let ls = String.concat "," ls in
    "CApp (" ^ cs ^ ",[" ^ ls ^ "])"
  | CProdN (l, c) ->
    let cs = string_of_constrexpr_r c.v in
    "CProdN (" ^ cs ^ ")"
  | CLambdaN (lbel, ce) ->
    "CLambdaN (" ^ string_of_local_binder_expr_list lbel ^ ", " ^ string_of_constrexpr_r ce.CAst.v ^ ")"
  | CLetIn (lname, ce1, None, ce2) ->
    "CLetIn (" ^ string_of_lname lname ^ "," ^ string_of_constrexpr_r ce1.CAst.v ^ ",None," ^ string_of_constrexpr_r ce2.CAst.v ^ ")"
  | CLetIn (lname, ce1, ceopt, ce2) ->
    "CLetIn (" ^ string_of_lname lname ^ "," ^ string_of_constrexpr_r ce1.CAst.v ^ "," ^ "<TODO: ceopt>," ^ string_of_constrexpr_r ce2.CAst.v ^ ")"
  | CNotation (scp, not, sub) ->
    let (_, s) = not in
    "CNotation (" ^ s ^ ")"
  | e -> "<not implemented" ^ string_of_constr_expr_label (CAst.make e) ^ ">"
  in string_of_constrexpr_r (e.CAst.v)
