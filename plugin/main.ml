open Constrexpr
open My_term
open Tomaparser
open Autorewrite
open Rewrite

(** 現在のゴールを、公理のうちいずれか一つを使って示す。
    ゴールは公理と等しいか、両辺を入れ替えたものである必要がある。*)
let tac_prove_by_axiom ~(axioms : Libnames.qualid list) =
  let open Proofview.Notations in
  let tactic_of axiom use_symmetry =
    Tactics.intros <*>
    (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC) <*>
    Tactics.apply (EConstr.mkRef (Nametab.global axiom, EConstr.EInstance.empty)) in
  let rec aux axioms use_symmetry =
    match axioms, use_symmetry with
    | hd :: tl, false ->
      Tacticals.tclORELSE
        (tactic_of hd use_symmetry)
        (aux axioms true)
    | hd :: tl, true ->
      Tacticals.tclORELSE
        (tactic_of hd use_symmetry)
        (aux tl false)
    | [], _ -> Tacticals.tclFAIL (Pp.str "Could not prove goal by axioms.") in
  aux axioms false

(** 公理のうちのどれかから直ちに導ける規則を証明する
    公理の一つと同じか、両辺を入れ替えたものである必要がある。*)
let prove_by_axiom ~name ~goal ~axioms =
  let env = Global.env () in 
  let sigma = Evd.from_env env in
  let (sigma, body) = Constrintern.interp_constr_evars env sigma goal in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let (t, types, uctx, obl_info) = Declare.Obls.prepare_obligation ~name ~types:None ~body sigma in
  let tactic = tac_prove_by_axiom ~axioms in
  let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx ~tactic obl_info in
  match progress with
  | Defined _ -> ()
  | _ -> failwith ("Could not prove axiom: " ^ (Names.Id.to_string name))

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

(*
  critical_pair による定理の証明
  name: 定理の名前
  n1: 証明に使う１つ目の定理名
  n2: 証明に使う２つ目の定理名
  l: 定理の左辺
  r: 定理の右辺
  crit: critical pair
*)
let proof_using_crit ~name ~n1 ~n2 ~l ~r ~crit ~(constants:constants option) =
  let constants = begin match constants with
  | None -> My_term.default_constants
  | Some cs -> cs
  end in
  let e = My_term.to_constrexpr_raw (l, r) constants in
  let evars = My_term.variables_except_constants (l, r) constants in
  let e1 = My_term.to_constrexpr_raw (crit, l) constants in
  let e1vars = My_term.variables_except_constants (crit, l) constants in
  let e2 = My_term.to_constrexpr_raw (crit, r) constants in
  let e2vars = My_term.variables_except_constants (crit, r) constants in
  let r1 = Libnames.qualid_of_string n1 in
  let r2 = Libnames.qualid_of_string n2 in
  let env = Global.env () in 
  let sigma = Evd.from_env env in
  let (sigma, body) = Constrintern.interp_constr_evars env sigma e in
  let (sigma, e1) = Constrintern.interp_constr_evars env sigma e1 in
  let (sigma, e2) = Constrintern.interp_constr_evars env sigma e2 in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let (t, types, ustate, obl_info) = Declare.Obls.prepare_obligation ~name ~types:None ~body sigma in
  let open Proofview.Notations in
  let open Equality in
  let open Tactypes in
  let rewriteLR c at =
    cl_rewrite_clause c true (OnlyOccurrences [at]) None in
  let explicit_bind v =
    if List.mem v evars then
      CAst.make (NamedHyp (CAst.make (Names.Id.of_string v)), (EConstr.mkVar (Names.Id.of_string v)))
    else
      (*
        Goal に含まれない変数の場合、rewriteタクティクのbind変数として使用すると Unbound のエラーが生じてしまう。
        Goal:A=C を ２つのB=A, B=Cで示す際に、Bのみに含まれる変数がある状況が該当する。
        このような状況で生じる変数は式変換の一部で現れ、結果に含まれないため、どの変数/定数でも良い。
        よって、定数とGoalの変数のうち一つを採用する。
      *)
      let binder = List.hd (evars @ (My_term.list_of_constants constants)) in
      CAst.make (NamedHyp (CAst.make (Names.Id.of_string v)), (EConstr.mkVar (Names.Id.of_string binder)))
  in
  let rewriteLR_with_binds c (vars : string list) =
    let binds = ExplicitBindings (List.map explicit_bind vars) in
    general_rewrite ~where:None ~l2r:true (OnlyOccurrences [1]) ~freeze:true ~dep:true ~with_evars:false (c, binds) in
  let rewriteRL_with_binds c (vars : string list) =
    let binds = ExplicitBindings (List.map explicit_bind vars) in
    general_rewrite ~where:None ~l2r:false (OnlyOccurrences [1]) ~freeze:true ~dep:true ~with_evars:false (c, binds) in
  let gen_tactic at1 at2 = Tactics.assert_by Names.Name.Anonymous e1 (
      Tactics.intros
      <*> rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r1, EConstr.EInstance.empty)), NoBindings)) at1
      <*> Tactics.reflexivity)
    <*> Tactics.assert_by Names.Name.Anonymous e2 (
      Tactics.intros
      <*> rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r2, EConstr.EInstance.empty)), NoBindings)) at2
      <*> Tactics.reflexivity)
    <*> Tactics.intros
    <*> rewriteRL_with_binds (EConstr.mkVar (Names.Id.of_string "H")) e1vars
    <*> rewriteLR_with_binds (EConstr.mkVar (Names.Id.of_string "H0")) e2vars
    <*> Tactics.reflexivity in
  let rec try_proof (at1, at2) =
    (* 自然数のペアに対して、次のペアを返す関数。 (1, 1)から始めると全てのペアを列挙する。 *)
    (* 例: (1, 1), (1, 2), (2, 2), (2, 1), (1, 3), ... *)
    let next_pair (x, y) =
      if y = 1 then
        (1, x + 1)
      else if x < y then (* 対角線より左側にある点 *)
        (x + 1, y)
      else 
        (x, y - 1)
    in
    let tactic = gen_tactic at1 at2 in
    let tactic = Proofview.tclORELSE tactic (fun _ -> Tacticals.tclIDTAC) in
    let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx:ustate ~tactic obl_info in
    begin match progress with
    | Remain _ -> try_proof (next_pair (at1, at2))
    | Dependent -> try_proof (next_pair (at1, at2))
    | Defined _ -> ()
    end
    in
  let () = try_proof (1, 1) in
    Pp.strbrk "Proof"

let cl_rewrite_clause_innermost ?(hyp:string = "H") (rewriter:Libnames.qualid) (left2right:bool) =
  let open Rewrite in
  let c_delayed = fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global rewriter, EConstr.EInstance.empty))) in
  let strat_ast = StratUnary (Innermost, StratConstr ((DAst.make (Glob_term.GVar (Names.Id.of_string "temp")), c_delayed), left2right)) in
  let strat = strategy_of_ast strat_ast in
  cl_rewrite_clause_strat strat (Some (Names.Id.of_string hyp))

(** 現在のゴールを冗長な規則の書換によって示す。 *)
let tac_prove_by_reduction ~(rewriters : Libnames.qualid list)
                           ~(rewritee : Libnames.qualid) =
  let open Proofview.Notations in
  (*
    項の左右方向に関わらず証明するため、N個の書き換え規則に対して、l2rs として N+1 個のboolの組み合わせを受け取る。
    l2rs[0]  : symmetry. を使用するかどうか
    l2rs[1:] : i個目の cl_rewrite_clause の書き換え方向を -> にするかどうかを l2rs[i] で表す。
    term の形を調べるかtomaの出力を修正すれば事前に書き換え方向は決定できそうだが、実装の簡単のため全ての組み合わせを試す。
   *)
  let tactic_of l2rs =
    let use_symmetry = List.hd l2rs in
    let l2rs = List.tl l2rs in
    Tactics.intros <*>
    Tactics.pose_proof (Names.Name (Names.Id.of_string "H")) (EConstr.mkRef (Nametab.global rewritee, EConstr.EInstance.empty)) <*>
    List.fold_left (fun prev cur -> prev <*> cur) Tacticals.tclIDTAC (
      List.map (fun (rewriter, l2r) -> 
        cl_rewrite_clause_innermost rewriter l2r
        ) (List.combine rewriters l2rs)) <*>
    (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC) <*>
    Auto.default_auto in
  let rec aux l2rs =
    Tacticals.tclORELSE
      (tactic_of l2rs)
      (match Devutil.next_binls l2rs with
      | None -> Tacticals.tclFAIL (Pp.str "Could not prove goal by reduction.")
      | Some l2rs -> aux l2rs) in
  aux (List.init (List.length rewriters + 1) (fun _ -> true))

let prove_interreduce
  ~(name:Names.Id.t) (* 証明する定理名 *)
  ~(goal:Constrexpr.constr_expr) (* 定理の型 *)
  ~(rewriters:Libnames.qualid list)
  ~(applier:Libnames.qualid) (* apply を行う定理名 *)
  =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let (sigma, body) = Constrintern.interp_constr_evars env sigma goal in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let (t, types, ustate, obl_info) = Declare.Obls.prepare_obligation ~name ~types:None ~body sigma in
  let tactic = tac_prove_by_reduction ~rewriters ~rewritee:applier in
  let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx:ustate ~tactic obl_info in
  match progress with
  | Defined _ -> ()
  | _ -> failwith ("Could not prove interreduce: " ^ (Names.Id.to_string name))

let add_rules_for_termination (rules : rule list) =
  let rec aux = function
  | [] -> ()
  | (id, (_, _)) :: tl ->
      let _ = add_local_rewrite_hint "hint_compl" (CAst.make (
        CRef (
          Libnames.qualid_of_string @@ "t" ^ id,
          None
        )
      )) in
      aux tl
  in aux rules

(* used in LPO, defined by toma output *)
let order_params = Summary.ref ~name:"order_params" []

let proof_using_toma (proc : procedure) (constants : constants option) axioms : string list =
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
  add_rules_for_termination rules;
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

let complete rs dbName ops =
  let axioms = List.map constr_of_qualid rs in
  (* path を付加する (例: "e" => "AutoEqProver.Test.e") *)
  let ops = List.map (fun op ->
    op |> Nametab.global |> Names.GlobRef.print |> Pp.string_of_ppcmds) ops in
  let outputs = Toma.toma axioms in
  let procedure = Tomaparser.parse outputs in
  let constantsopt: constants option = Some (My_term.constants_of_list ops) in
  let outputs = proof_using_toma procedure constantsopt rs in
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
  | `Func i, `Func j -> if i > j then GR else if i = j then EQ else NGE
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
