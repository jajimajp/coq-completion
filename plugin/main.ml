open Constrexpr
open My_term
open Tomaparser
open Autorewrite
open Rewrite
open Coq_intf

(* for exporting *)
let prove_interreduce = prove_interreduce

let add_axiom (rule : rule) (constants : constants option) axioms =
  let name = Names.Id.of_string ("t" ^ fst rule) in
  let constants = (match constants with None -> My_term.default_constants | Some cs -> cs) in
  let goal = My_term.to_constrexpr_raw (fst (snd rule), snd (snd rule)) constants in
  let () = prove_by_axiom ~name ~goal ~axioms in
  ()

(*
  書換規則をヒントDBに追加する

  base ヒントDB名
  lcsr 定理を表す項

  extratactics.mlg を参考に実装
  簡単のため、"->" のみで、"using"は使わず、local で宣言するようにしている
*)
let add_local_rewrite_hint (base: string) (lcsr: Constrexpr.constr_expr) : Pp.t =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let f ce =
    let c, ctx = Constrintern.interp_constr env sigma ce in
    let c = EConstr.to_constr sigma c in
    let ctx =
      let ctx = UState.context_set ctx in
        (DeclareUctx.declare_universe_context ~poly:false ctx;
          Univ.ContextSet.empty)
    in
      CAst.make ?loc:(Constrexpr_ops.constr_loc ce) ((c, ctx), (* ort *) true, (* t *) None) in
  let eq = f lcsr in
  let add_hints base = add_rew_rules ~locality:Local base [eq] in
  let _ = add_hints base in
  Pp.strbrk "Added rewrite hints."

let add_rules_for_termination (rules : rule list) (hint_db_name : string) =
  let rec aux = function
  | [] -> ()
  | (id, (_, _)) :: tl ->
      let _ = add_local_rewrite_hint hint_db_name (CAst.make (
        CRef (
          Libnames.qualid_of_string @@ "t" ^ id,
          None
        )
      )) in
      aux tl
  in aux rules

(* used in LPO, defined by toma output *)
let order_params = Summary.ref ~name:"order_params" []

let proof_using_toma (proc : procedure) (constants : constants option) axioms hint_db_name : string list =
  let open Tomaparser in
  let (proofs, _, _) = proc in
  let prove (rule, strat) = match strat with
  | Axiom ->
    add_axiom rule constants axioms
  | Crit (r1, r2, crit) ->
    let n1 = "t" ^ (fst r1) in
    let n2 = "t" ^ (fst r2) in
    ignore @@ proof_using_crit ~name:(Names.Id.of_string ("t" ^ fst rule)) ~n1 ~n2 ~l:(fst (snd rule)) ~r:(snd (snd rule)) ~crit ~constants
  | Simp (prev, rewriters) ->
    let constants = (match constants with None -> My_term.default_constants | Some cs -> cs) in
    ignore @@ prove_interreduce ~name:(Names.Id.of_string ("t" ^ (fst rule)))
                                ~goal:(My_term.to_constrexpr_raw (snd rule) constants)
                                ~rewriters:(List.map (fun id -> Libnames.qualid_of_string ("t" ^ id)) rewriters)
                                ~applier:(Libnames.qualid_of_string ("t" ^ (fst prev))) in
  List.iter prove proofs; 
  let _, rules, _ = proc in
  add_rules_for_termination rules hint_db_name;
  let _, _, op = proc in
  order_params := op;
  []

let get_constant_body gref =
  let open Names.GlobRef in
  match gref with
  | ConstRef cst ->
    let cb = Global.lookup_constant cst in
    cb
  | _ -> failwith "Invalid input"

let constr_of_qualid (ln: Libnames.qualid): Constr.t =
  let gref = Nametab.global ln in
  let cb = get_constant_body gref in
  cb.const_type

let complete rs hint_db_name ops =
  let axioms = List.map constr_of_qualid rs in
  (* path を付加する (例: "e" => "AutoEqProver.Test.e") *)
  let ops = List.map (fun op ->
    op |> Nametab.global |> Names.GlobRef.print |> Pp.string_of_ppcmds) ops in
  let outputs = Toma.toma axioms in
  let procedure = Tomaparser.parse outputs in
  let constantsopt: constants option = Some (My_term.constants_of_list ops) in
  let outputs = proof_using_toma procedure constantsopt rs hint_db_name in
  Pp.str @@ String.concat "\n" outputs

open Equality
open Pp
open Tacticals

let eq_of_constr (t : Constr.t) : My_term.t =
  My_term.of_constr t

let eq_of_goal (gl : Proofview.Goal.t) : My_term.t =
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  eq_of_constr (EConstr.to_constr sigma concl)
 
type order
  = GR  (* x > y *)
  | EQ  (* x = y *)
  | NGE (* not (x >= y) *)

let rec lex ord (xs, ys) =
  match xs, ys with
  | [], [] -> EQ
  | x :: xs, y :: ys ->
    begin
      match ord (x, y) with
      | GR -> GR
      | EQ -> lex ord (xs, ys)
      | NGE -> NGE
    end
  | _ -> failwith "[lex ord (xs, ys)]: length differs between xs and ys."

let rec occurs x t =
  match t with
  | Var y -> x = y
  | App (f, ts) ->
    List.exists (occurs x) ts

let rec lpo ord (s, t) =
  match s, t with
  | _, Var x -> if s = t then EQ
                else if occurs x s then GR
                else NGE
  | Var _, App _ -> NGE
  | App (f, ss), App (g, ts) ->
    let forall f ls = not (List.exists (fun e -> not (f e)) ls) in
    if forall (fun si -> lpo ord (si, t) = NGE) ss
    then
      begin match ord (f, g) with
      | GR -> if forall (fun ti -> lpo ord (s, ti) = GR) ts
              then GR else NGE
      | EQ -> if forall (fun ti -> lpo ord (s, ti) = GR) ts
              then lex (lpo ord) (ss, ts)
              else NGE
      | NGE -> NGE
      end
    else GR

let rec skolemize = function
| Var x -> App (x, [])
| App (f, ts) -> App (f, List.map skolemize ts)

let skolemize_eq eq =
  let (s, t) = eq in
  (skolemize s, skolemize t)

let ord (a, b) = 
  let find_index f ls =
    let rec aux i = function
    | [] -> raise Not_found
    | hd :: tl -> if f hd then i else aux (i + 1) tl
    in aux 0 ls in
  let rank s =
    if List.mem s !order_params then `Func (find_index (fun x -> x = s) !order_params)
    else `Var s in
  match rank a, rank b with
  | `Func i, `Func j -> if i < j then GR else if i = j then EQ else NGE
  | `Func _, `Var _ -> GR
  | `Var _, `Func _ -> NGE
  | `Var x, `Var y -> if x > y then GR else if x = y then EQ else NGE

let lpogt a b =
  let a = skolemize_eq a in
  let b = skolemize_eq b in
  match (lpo ord (fst a, fst b)), (lpo ord (snd a, snd b)) with
  | GR, _ -> GR
  | _, GR -> GR
  | EQ, EQ -> EQ
  | _, _ -> NGE

let tclMAP_rev f args =
  List.fold_left (fun accu arg -> Tacticals.tclTHEN accu (f arg)) (Proofview.tclUNIT ()) args

exception NotReducingOrder
let tclVALIDATE_LPO t =
  Proofview.Goal.enter (fun pre -> 
  Tacticals.tclTHEN t (
    Proofview.Goal.enter (fun gl -> 
      match lpogt (eq_of_goal pre) (eq_of_goal gl) with
      | GR ->  tclIDTAC
      | _ -> raise NotReducingOrder
      )))

let tclPROTECT_LPO t =
  let open Proofview in
  let open Proofview.Notations in
  let t = 
    Proofview.Goal.enter (fun pre -> 
    Tacticals.tclTHEN t (
      Proofview.Goal.enter (fun gl -> 
        match lpogt (eq_of_goal pre) (eq_of_goal gl) with
        | GR -> tclIDTAC
        | _ -> Tacticals.tclFAIL (Pp.str "Not reducing rewriting"
        ))))
      in
    Proofview.tclIFCATCH t
      (fun () -> tclIDTAC)
      (fun e -> catch_failerror e <*> tclUNIT ())

let one_base where conds tac_main bas =
  let lrul = find_rewrites bas in
  let rewrite dir c tac =
    let c = fun env sigma -> sigma, (EConstr.of_constr c, Tactypes.NoBindings) in
    try
      let rec tac at =
        let t = cl_rewrite_clause c dir (OnlyOccurrences [at]) where in
        Proofview.tclIFCATCH (tclPROGRESS (tclVALIDATE_LPO t))
          (fun () -> tclIDTAC)
          (function
          | (NotReducingOrder, _) -> tac (at + 1) (* Could rewrite but not valid rewriting order, so we should check other occurences. *)
          | _ -> Proofview.tclUNIT ()) (* other errors which includes "Invalid Occurrences", which means we checked all occurrences for c. *)
        in
      tac 1
    with e -> tclIDTAC
  in
  let try_rewrite h tc =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let rew_ctx, rew_lemma = RewRule.rew_lemma h in
    let subst, ctx' = UnivGen.fresh_universe_context_set_instance rew_ctx in
    let c' = Vars.subst_univs_level_constr subst rew_lemma in
    let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx' in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) (rewrite (RewRule.rew_l2r h) c' tc)
  end in
  let open Proofview.Notations in
  Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (_name, poly) ->
  let eval h =
    let rew_tac = RewRule.rew_tac h in
    let tac = match rew_tac with
    | None -> Proofview.tclUNIT ()
    | Some (Genarg.GenArg (Genarg.Glbwit wit, tac)) ->
      let ist = { Geninterp.lfun = Names.Id.Map.empty
                ; poly
                ; extra = Geninterp.TacStore.empty } in
      Ftactic.run (Geninterp.interp wit ist tac) (fun _ -> Proofview.tclUNIT ())
    in
    Tacticals.tclREPEAT_MAIN @@
      tclPROTECT_LPO @@
        (Tacticals.tclTHENFIRST (try_rewrite h tac) tac_main)
  in
  let lrul = tclMAP_rev eval lrul in
  Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS lrul)

let autorewrite ?(conds=Naive) tac_main hint =
  Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (one_base None conds tac_main hint))

let autorewrite_multi_in ?(conds=Equality.Naive) idl tac_main lbas =
  Proofview.Goal.enter begin fun gl ->
    (* let's check at once if id exists (to raise the appropriate error) *)
    let _ = List.map (fun id -> Tacmach.pf_get_hyp id gl) idl in
    Tacticals.tclMAP (fun id ->
    Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS
      (tclMAP_rev (fun bas -> (one_base (Some id) conds tac_main bas)) lbas)))
      idl
  end

open Locus
let gen_auto_multi_rewrite conds tac_main lbas cl =
  let bas = List.hd lbas in
  let try_do_hyps treat_id l =
    autorewrite_multi_in ~conds (List.map treat_id l) tac_main lbas
  in
  let concl_tac = (if cl.concl_occs != NoOccurrences then autorewrite ~conds tac_main bas else Proofview.tclUNIT ()) in
  if not (Locusops.is_all_occurrences cl.concl_occs) &&
     cl.concl_occs != NoOccurrences
  then
    let info = Exninfo.reify () in
    Tacticals.tclZEROMSG ~info (str "The \"at\" syntax isn't available yet for the autorewrite tactic.")
  else
    match cl.onhyps with
    | Some [] -> concl_tac
    | Some l -> Tacticals.tclTHENFIRST concl_tac (try_do_hyps (fun ((_,id),_) -> id) l)
    | None ->
      let hyp_tac =
        (* try to rewrite in all hypothesis (except maybe the rewritten one) *)
        Proofview.Goal.enter begin fun gl ->
          let ids = Tacmach.pf_ids_of_hyps gl in
          try_do_hyps (fun id -> id)  ids
        end
      in
      Tacticals.tclTHENFIRST concl_tac hyp_tac

let auto_multi_rewrite ?(conds=Naive) lems cl =
  Proofview.wrap_exceptions
    (fun () -> gen_auto_multi_rewrite conds (Proofview.tclUNIT()) lems cl)

let lpo_autorewrite_with hintDb cl =
  (auto_multi_rewrite [hintDb] cl) 

let complete_in_tac axs cs cl =
  let axs = List.map Libnames.qualid_of_string axs in
  let cs = List.map Libnames.qualid_of_string cs in
  let axioms = List.map constr_of_qualid axs in
  (* path を付加する (例: "e" => "AutoEqProver.Test.e") *)
  let ops = List.map (fun op ->
    op |> Nametab.global |> Names.GlobRef.print |> Pp.string_of_ppcmds) cs in
  let outputs = Toma.toma axioms in
  let procedure = Tomaparser.parse outputs in
  let constantsopt: constants option = Some (My_term.constants_of_list ops) in
  let _ = proof_using_toma procedure constantsopt axs "hint_compl" in
  Proofview.tclUNIT ()

let complete_for (goal :Constrexpr.constr_expr) rs hint_db_name ops =
  let axioms = List.map constr_of_qualid rs in
  (* path を付加する (例: "e" => "AutoEqProver.Test.e") *)
  let ops = List.map (fun op ->
    op |> Nametab.global |> Names.GlobRef.print |> Pp.string_of_ppcmds) ops in
  let env = Global.env () in 
  let sigma = Evd.from_env env in
  let (sigma, goal) = Constrintern.interp_constr_evars env sigma goal in
  let goal = EConstr.to_constr sigma goal in
  let outputs = Toma.toma_with_goal ~goal axioms in
  let pl, gl, ord = Tomaparser.parse_for_goal outputs in
  let rules = List.map (fun (r, _) -> r) pl in
  let procedure = pl, rules, ord in
  let constantsopt: constants option = Some (My_term.constants_of_list ops) in
  let outputs = proof_using_toma procedure constantsopt rs hint_db_name in
  Pp.str @@ String.concat "\n" outputs