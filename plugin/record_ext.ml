open Names
open Pp


let string_of_constr_label constr =
  match Constr.kind constr with
  | Constr.Rel _ -> "Rel"
  | Var _ -> "Var"
  | Meta _ -> "Meta"
  | Evar _ -> "Evar"
  | Sort _ -> "Sort"
  | Cast _ -> "Cast"
  | Prod _ -> "Prod"
  | Lambda _ -> "Lambda"
  | LetIn _ -> "LetIn"
  | App _ -> "App"
  | Const _ -> "Const"
  | Ind _ -> "Ind"
  | Construct _ -> "Construct"
  | Case _ -> "Case"
  | Fix _ -> "Fix"
  | CoFix _ -> "CoFix"
  | Proj _ -> "Proj"
  | Int _ -> "Int"
  | Float _ -> "Float"
  | String _ -> "String"
  | Array _ -> "Array"

module ConstantSort = struct
  type constant = Names.Constant.t
  type t = Type | Operator | Axiom

  let rec of_constant env sigma (const : constant) =
    let is_type (const : constant) =
      let constant_body = Environ.lookup_constant const env in
      (* Type is constant with const_type (Sort _) *)
      match Constr.kind constant_body.const_type with
      | Constr.Sort _ -> true
      | _ -> false
    in

    if is_type const then Type
    else if is_operator env sigma const then Operator
    else Axiom
  (* NOTE: this does not validate [const] has correct axiom form. *)

  and is_operator env sigma const =
    let constant_body = Environ.lookup_constant const env in
    is_operator_constr env sigma constant_body.const_type

  and is_operator_constr env sigma constr =
    match Constr.kind constr with
    | Prod (binder, _, c) -> is_operator_constr env sigma c
    | Const _ -> true (* "e" for example *)
    | App _ -> false (* assume _ = _ *)
    | Ind _ -> true
    | _ -> false (* e + e = e will go here for example *)

  let to_string = function
    | Type -> "Type"
    | Operator -> "Operator"
    | Axiom -> "Axiom"

  let print t = Pp.str (to_string t)
end

let get_constant_ref = function
  | Names.GlobRef.ConstRef const -> const
  | ConstructRef _ -> failwith "get_construct_ref: IndRef not implemented"
  | IndRef _ -> failwith "get_constant_ref: IndRef not implemented"
  | VarRef _ -> failwith "get_constant_ref: VarRef not implemented"

let get_constant_def_constr = function
  | Declarations.Def constr -> constr
  | _ -> failwith "get_constant_def_constr: Not implemented"

let pr_constant_def_label = function
  | Declarations.Undef _inline -> Pp.str "Undef"
  | Def _a -> Pp.str "Def"
  | OpaqueDef _opaque -> Pp.str "OpaqueDef"
  | Primitive _prim -> Pp.str "Primitive"
  | Symbol _rules -> Pp.str "Symbol"

type extracted = {
  typ : Names.Constant.t option;
      (* "G" for example. NOTE: this is currently not provided because not used. *)
  ops : Constr.t list (* ["e"; "i"; "f"] for example *);
  axioms : Names.Constant.t list (* ["id_l"; "inv_l"; "assoc"] for example *);
}
(** Extracted constants of given record *)

let sort_constant env sigma (const : Names.Constant.t) =
  let constant_body = Environ.lookup_constant const env in
  let const_typ = constant_body.const_type in
  Feedback.msg_debug
    Pp.(
      str "[sort]: " ++ str "; const=" ++ Names.Constant.print const
      ++ str "; const_typ="
      ++ (Printer.pr_constr_env env sigma const_typ
         ++ str "; const_typ label="
         ++ str (string_of_constr_label const_typ)
         ++ str "; sort="
         ++ (ConstantSort.of_constant env sigma const |> ConstantSort.print)))

(** [extract env sigma record] extracts type name, function symbols and equations. *)
let extract : Environ.env -> Evd.evar_map -> Libnames.qualid -> extracted =
 fun env sigma record ->
  match Constrintern.locate_reference record with
  | None ->
      failwith
        (Printf.sprintf "extract: record %s not found."
           (Libnames.string_of_qualid record))
  | Some gref ->
      let const = get_constant_ref gref in
      let constant_body = Environ.lookup_constant const env in
      let constant_def = constant_body.const_body in
      let constr = get_constant_def_constr constant_def in
      let (* App *) f, args = Constr.destApp constr in

      let typ = ref None in
      let ops = ref [] in
      let axioms = ref [] in
      let () =
        Array.iter
          (fun arg ->
            match Constr.kind arg with
            | Const _ -> (
                let const, _univ = Constr.destConst arg in
                match ConstantSort.of_constant env sigma const with
                | Type ->
                    if !typ != None then
                      failwith "extract: multiple sorts found."
                    else typ := Some const
                | Operator -> ops := arg :: !ops
                | Axiom -> axioms := const :: !axioms)
            | Ind _ ->
                (* failwith "extract: not implemented for Ind" *)
                ()
                (* TODO: Treating Ind as typ and ignore *)
            | Construct _ ->
                (* failwith "extract: not implemented for Construct" *)
                ops := arg :: !ops (* TODO: Treating Construct as ops *)
            | _ -> failwith "extract: not implemented")
          args
      in
      { typ = !typ; ops = !ops; axioms = !axioms }


let show_inductive env ind =
  let (mutind, i) = ind in
  if i <> 0 then failwith "Mutualy recursive induction is not supported" else
    Feedback.msg_notice (str"show_inductive " ++ str (MutInd.debug_to_string mutind));
  let (mb, b) = Inductive.lookup_mind_specif env ind in
    Feedback.msg_notice (str"mutual inductive body: " ++ int (mb.mind_ntypes));
    Feedback.msg_notice (str"inductive body: " ++
      str"typename: " ++ Id.print (b.mind_typename) ++spc()++
      str"nrealdecls: " ++ int (b.mind_nrealdecls) ++spc()++
      str"nrealargs: " ++ int (b.mind_nrealargs));
  match mb.mind_record with
  | PrimRecord _ ->
    Feedback.msg_notice (str"prim")
  | _ ->
      Feedback.msg_notice (str"not prim");
  let ta = Inductive.type_of_constructors (UVars.in_punivs ind) (mb, b) in
  Array.iter begin fun elem ->
    let sigma = Evd.from_env env in
    Feedback.msg_notice (str"+ " ++ Printer.pr_constr_env env sigma elem ++spc())
  end ta;
  let ctxt = mb.mind_params_ctxt in
  List.iter begin fun decl ->
    let nam = Context.Rel.Declaration.get_name decl in
    let typ = Context.Rel.Declaration.get_type decl in
    let sigma = Evd.from_env env in
    Feedback.msg_notice (str"% " ++ Name.print nam ++ spc() ++ Printer.pr_constr_env env sigma typ ++spc())
  end ctxt;
  let ctxt = b.mind_arity_ctxt in
  List.iter begin fun decl ->
    let nam = Context.Rel.Declaration.get_name decl in
    let typ = Context.Rel.Declaration.get_type decl in
    let sigma = Evd.from_env env in
    Feedback.msg_notice (str"* " ++ Name.print nam ++ spc() ++ Printer.pr_constr_env env sigma typ ++spc())
  end ctxt;
  let nf_lc = b.mind_nf_lc in
  Array.iter begin fun (ctx, typ) ->
    let sigma = Evd.from_env env in
    List.iter begin fun decl ->
      let nam = Context.Rel.Declaration.get_name decl in
      let typ = Context.Rel.Declaration.get_type decl in
      let sigma = Evd.from_env env in
      Feedback.msg_notice (str"  # " ++ Name.print nam ++ spc() ++ Printer.pr_constr_env env sigma typ ++spc())
    end ctxt;
    Feedback.msg_notice (str"  - " ++ Printer.pr_constr_env env sigma typ ++spc())
  end nf_lc;
  Array.iter begin fun nam ->
    Feedback.msg_notice (str"  [N] " ++ Id.print nam)
  end b.mind_consnames


let show_record : Environ.env -> Evd.evar_map ->  Libnames.qualid -> unit =
  fun env sigma record ->
    match Constrintern.locate_reference record with
    | None -> ()
    | Some (IndRef inductive) ->
        Feedback.msg_info (str"show_record:Ind "++ Printer.pr_inductive env inductive);
        show_inductive env inductive
    | Some (ConstructRef cstr) ->
        Feedback.msg_info (str"show_record:Construct "++ Printer.pr_constructor env cstr);
        failwith "Not implemented"
    | Some (ConstRef const) ->
        Feedback.msg_info (str"show_record:Const "++ Printer.pr_constant env const);
        failwith "Not implemented"
    | _ -> failwith "Not implemented"

