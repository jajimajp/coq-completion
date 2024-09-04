open Rewrite

(** [tclPRINT_GOAL] prints current goal. *)
let tclPRINT_GOAL s =
  Proofview.Goal.enter (fun gl ->
      print_endline @@ "PRINT_GOAL " ^ s;
      let open Proofview.Goal in
      let sigma, env, hyps = (sigma gl, env gl, hyps gl) in
      let hyps =
        hyps
        |> Context.Named.fold_outside
             ~init:Pp.(str "・")
             (fun pt acc ->
               let id = Context.Named.Declaration.get_id pt in
               let id = Names.Id.print id in
               let econstr = Context.Named.Declaration.get_type pt in
               Pp.(
                 acc ++ str ", " ++ id ++ str ": "
                 ++ Printer.pr_econstr_env env sigma econstr))
      in
      let concl = concl gl in
      Feedback.msg_notice
        Pp.(
          str "hyps: " ++ hyps ++ str ", goal: "
          ++ Printer.pr_econstr_env env sigma concl);
      Proofview.tclUNIT ())

(** [constr_of_s s] は識別子 [s] の項を取得する。
    HACK: もっと簡潔に書けそう。 *)
let const_of_s s : Names.Constant.t =
  let ln = Libnames.qualid_of_string s in
  let gref = Nametab.global ln in
  let open Names.GlobRef in
  match gref with ConstRef cst -> cst | _ -> failwith "Invalid input"

let cl_rewrite_clause_innermost ?(hyp : string = "H")
    (rewriter : Libnames.qualid) (left2right : bool) =
  let open Rewrite in
  let c_delayed env sigma =
    (sigma, EConstr.mkRef (Nametab.global rewriter, EConstr.EInstance.empty))
  in
  let strat_ast =
    StratUnary
      ( Innermost,
        StratConstr
          ( (DAst.make (Glob_term.GVar (Names.Id.of_string "temp")), c_delayed),
            left2right ) )
  in
  let strat = strategy_of_ast strat_ast in
  cl_rewrite_clause_strat strat (Some (Names.Id.of_string hyp))

(** 現在のゴールを、公理のうちいずれか一つを使って示す。
    ゴールは公理と等しいか、両辺を入れ替えたものである必要がある。*)
let tac_prove_by_axiom ~(axioms : Libnames.qualid list) =
  let open Proofview.Notations in
  let tactic_of axiom use_symmetry =
    Tactics.intros
    <*> (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC)
    <*> Tactics.apply
          (EConstr.mkRef (Nametab.global axiom, EConstr.EInstance.empty))
  in
  let rec aux axioms use_symmetry =
    match axioms with
    | [] -> Tacticals.tclFAIL (Pp.str "Could not prove goal by axioms.")
    | hd :: tl ->
        Tacticals.tclIFCATCH
          (Tacticals.tclPROGRESS (tactic_of hd use_symmetry))
          (fun _ -> Tacticals.tclIDTAC)
          (fun _ ->
            match use_symmetry with
            | false -> aux axioms true
            | true -> aux tl false)
  in
  aux axioms false

let prove_by_axiom ~name ~goal ~axioms =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, body = Constrintern.interp_constr_evars env sigma goal in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let t, types, uctx, obl_info =
    Declare.Obls.prepare_obligation ~name ~types:None ~body sigma
  in
  let tactic = tac_prove_by_axiom ~axioms in
  let _, progress =
    Declare.Obls.add_definition ~pm:Declare.OblState.empty ~cinfo ~info ~uctx
      ~tactic obl_info
  in
  match progress with
  | Defined _ -> ()
  | _ -> failwith ("Could not prove axiom: " ^ Names.Id.to_string name)

let tac_prove_by_crit ~evars ~constants ~e1 ~e2 ~r1 ~r2 ~crit ~l ~r =
  let e1vars = My_term.variables_except_constants (crit, l) constants in
  let e2vars = My_term.variables_except_constants (crit, r) constants in
  let open Proofview.Notations in
  let open Equality in
  let open Tactypes in
  let rewriteLR c at = cl_rewrite_clause c true (OnlyOccurrences [ at ]) None in
  let explicit_bind v =
    if List.mem v evars then
      CAst.make
        ( NamedHyp (CAst.make (Names.Id.of_string v)),
          EConstr.mkVar (Names.Id.of_string v) )
    else
      (*
        Goal に含まれない変数の場合、rewriteタクティクのbind変数として使用すると Unbound のエラーが生じてしまう。
        Goal:A=C を ２つのB=A, B=Cで示す際に、Bのみに含まれる変数がある状況が該当する。
        このような状況で生じる変数は式変換の一部で現れ、結果に含まれないため、どの変数/定数でも良い。
        よって、定数とGoalの変数のうち一つを採用する。
      *)
      let binder =
        match evars with
        | h :: _ -> EConstr.mkVar (Names.Id.of_string h)
        | [] -> (
            (* If there are not evars, use constants. *)
            let rec last = function
              | [] -> raise Not_found
              | [ x ] -> x
              | h :: t -> last t
            in
            match My_term.list_of_constants constants with
            | [] -> failwith "tac_prove_by_crit: No constants."
            | h :: _ ->
                let binder = last (String.split_on_char '.' h) in
                EConstr.mkConstU (const_of_s binder, EConstr.EInstance.empty))
      in
      CAst.make (NamedHyp (CAst.make (Names.Id.of_string v)), binder)
  in
  let rewriteLR_with_binds c (vars : string list) =
    let binds = ExplicitBindings (List.map explicit_bind vars) in
    general_rewrite ~where:None ~l2r:true (OnlyOccurrences [ 1 ]) ~freeze:true
      ~dep:true ~with_evars:false (c, binds)
  in
  let rewriteRL_with_binds c (vars : string list) =
    let binds = ExplicitBindings (List.map explicit_bind vars) in
    general_rewrite ~where:None ~l2r:false (OnlyOccurrences [ 1 ]) ~freeze:true
      ~dep:true ~with_evars:false (c, binds)
  in
  let _ =
    (* prevent warn *)
    let _ =
      rewriteLR
        (fun env sigma ->
          ( sigma,
            ( EConstr.mkRef (Nametab.global r1, EConstr.EInstance.empty),
              NoBindings ) ))
        1
    in
    let _ =
      rewriteLR_with_binds (EConstr.mkVar (Names.Id.of_string "H")) e1vars
    in
    let _ =
      rewriteRL_with_binds (EConstr.mkVar (Names.Id.of_string "H")) e2vars
    in
    ()
  in
  let tactic_of at1 at2 =
    (* Tactics.assert_by Names.Name.Anonymous e1 (
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
       <*> Tactics.reflexivity *)
    Tactics.assert_by
      (Names.Name.mk_name (Names.Id.of_string "H_0"))
      e1
      (Tactics.intros
      <*> rewriteLR
            (fun env sigma ->
              ( sigma,
                ( EConstr.mkRef (Nametab.global r1, EConstr.EInstance.empty),
                  NoBindings ) ))
            at1
      <*> Tactics.reflexivity)
    <*> Tactics.assert_by
          (Names.Name.mk_name (Names.Id.of_string "H_1"))
          e2
          (Tactics.intros
          <*> rewriteLR
                (fun env sigma ->
                  ( sigma,
                    ( EConstr.mkRef (Nametab.global r2, EConstr.EInstance.empty),
                      NoBindings ) ))
                at2
          <*> Tactics.reflexivity)
    <*> Tactics.intros
    <*> rewriteRL_with_binds (EConstr.mkVar (Names.Id.of_string "H_0")) e1vars
    <*> rewriteLR_with_binds (EConstr.mkVar (Names.Id.of_string "H_1")) e2vars
    <*> Tactics.reflexivity
    (* <*> Tacticals.tclIDTAC *)
  in
  (* 自然数のペアに対して、次のペアを返す関数。 (1, 1)から始めると全てのペアを列挙する。 *)
  (* 例: (1, 1), (1, 2), (2, 2), (2, 1), (1, 3), ... *)
  let next_pair (x, y) =
    (* fail *)
    if x = 10 then failwith "fail: Too many pairs."
    else if y = 1 then (1, x + 1)
    else if x < y then (* 対角線より左側にある点 *)
      (x + 1, y)
    else (x, y - 1)
  in
  let rec aux (at1, at2) =
    (* let aux (at1, at2) = *)
    (* (tactic_of at1 at2) in *)
    Tacticals.tclIFCATCH
      (try Tacticals.tclPROGRESS (tactic_of at1 at2)
       with exn ->
         print_endline ("xn: " ^ Printexc.to_string exn);
         Tacticals.tclFAIL (Pp.str "fl"))
      (fun _ -> Tacticals.tclIDTAC)
      (fun _ -> aux (next_pair (at1, at2)))
  in
  aux (1, 1)

(*
  critical_pair による定理の証明
  name: 定理の名前
  n1: 証明に使う１つ目の定理名
  n2: 証明に使う２つ目の定理名
  l: 定理の左辺
  r: 定理の右辺
  crit: critical pair
*)
let proof_using_crit ~name ~n1 ~n2 ~l ~r ~crit
    ~(constants : My_term.constants option) =
  let constants =
    match constants with None -> My_term.default_constants | Some cs -> cs
  in
  let e = My_term.to_constrexpr_raw (l, r) constants in
  let evars = My_term.variables_except_constants (l, r) constants in
  let e1 = My_term.to_constrexpr_raw (crit, l) constants in
  let e2 = My_term.to_constrexpr_raw (crit, r) constants in
  let r1 = Libnames.qualid_of_string n1 in
  let r2 = Libnames.qualid_of_string n2 in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, body = Constrintern.interp_constr_evars env sigma e in
  let sigma, e1 = Constrintern.interp_constr_evars env sigma e1 in
  let sigma, e2 = Constrintern.interp_constr_evars env sigma e2 in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let t, types, ustate, obl_info =
    Declare.Obls.prepare_obligation ~name ~types:None ~body sigma
  in
  let tactic =
    tac_prove_by_crit ~evars ~constants ~e1 ~e2 ~r1 ~r2 ~crit ~l ~r
  in
  let _, progress =
    Declare.Obls.add_definition ~pm:Declare.OblState.empty ~cinfo ~info
      ~uctx:ustate ~tactic obl_info
  in
  match progress with
  | Defined _ -> ()
  | _ -> failwith ("Could not prove goal by crit: " ^ Names.Id.to_string name)

let hyps_contains_free_prod_env env sigma hyps =
  (* HACK: econstr としては G -> ... も forall a : G, ... もどちらも Prod になるが、
     extern すると G -> ... は Notation になることを利用する。 *)
  Context.Named.fold_inside ~init:false
    (fun acc pt ->
      let econstr = Context.Named.Declaration.get_type pt in
      if not @@ EConstr.isProd sigma econstr then false
      else
        let cexpr = Constrextern.extern_constr env sigma econstr in
        match cexpr.CAst.v with CNotation _ -> true | _ -> acc)
    hyps

let const_body_type = function
  | Declarations.Def c -> EConstr.of_constr c
  | Declarations.Undef None ->
      print_endline "GOT UNDEF";
      failwith "Invalid input"
  | Declarations.Undef (Some i) ->
      print_endline "GOT UNDEF";
      failwith "Invalid input"
  | Declarations.OpaqueDef _ ->
      print_endline "GOT OPAQUE";
      failwith "Invalid input"
  | Declarations.Primitive _ ->
      print_endline "GOT PRIMITIVE";
      failwith "Invalid input"

let tclSPECIALIZE_IF_NECESSARY next =
  let open Proofview.Notations in
  Proofview.Goal.(
    enter_one (fun gl ->
        let sigma, env, hyps = (sigma gl, env gl, hyps gl) in
        if hyps_contains_free_prod_env env sigma hyps then (
          let _ = print_endline "P" in
          let c =
            try Environ.lookup_constant (const_of_s "a1") env
            with Not_found -> failwith "Could not find constant a1"
          in
          Feedback.msg_notice
            Pp.(
              str "Specialize: "
              ++ Printer.pr_econstr_env env sigma
                   (EConstr.of_constr c.const_type));
          Auto.h_auto None
            [
              (fun env sigma ->
                let c = Environ.lookup_constant (const_of_s "a1") env in
                let c = const_body_type c.const_body in
                Feedback.msg_notice
                  Pp.(str "Specialize: " ++ Printer.pr_econstr_env env sigma c);
                (sigma, c));
            ]
            None
          <*> Proofview.Goal.(
                enter_one (fun gl ->
                    print_endline "HELLO?";
                    let sigma = sigma gl in
                    let env = env gl in
                    let hyps = hyps gl in
                    let () =
                      hyps
                      |> Context.Named.fold_outside ~init:() (fun pt () ->
                             let id = Context.Named.Declaration.get_id pt in
                             let id = Names.Id.print id in
                             let econstr =
                               Context.Named.Declaration.get_type pt
                             in
                             Feedback.msg_notice
                               Pp.(
                                 str "hyp(" ++ id ++ str ") "
                                 ++ Printer.pr_econstr_env env sigma econstr))
                    in
                    if hyps_contains_free_prod_env env sigma hyps then
                      Proofview.tclUNIT (Feedback.msg_notice Pp.(str "YY"))
                      <*> next
                    else Proofview.tclUNIT (Feedback.msg_notice Pp.(str "NN"))))
          <*> next)
        else next))

exception Prove_failed

(** 連続する rewrite の [i] 番目でエラーが出たことを表す。 *)
exception RewriteFailAt of int

(** [tclPROVE_BY_REDUCTION ~name ~goal ~rewritee ~rewrites] proves current goal by rewriting [rewritee] with [rewriters].
    This tactic is like [tac_prove_by_reduction], but this searches more patterns than [tac_prove_by_reduction].
    @param name The name of the theorem to prove.
    @param goal The goal to prove.
    @rewritee The name of the rewrite rule to use.
    @rewriters The list of the rewrite rules to use. *)
let tclPROVE_BY_REDUCTION ~name ~goal ~rewritee ~rewriters =
  let rewrite c at l2r =
    cl_rewrite_clause c l2r (OnlyOccurrences [ at ]) (Some (Names.Id.of_string "H")) in
  (* パラメータを変えながら成功するまで試す。
     変更する変数は次の通り:
     - use_symmetry: symmetry を使うかどうか。H と goal の両辺が逆になるケースに対応するため。
     - l2rs: 各 rewrite rule に対して、左右どちらに書き換えるか。
     - ats: 各 rewrite rule をどの箇所に適用するか。Coq の rewrite at ... に対応する。
     - full: at を全探索するかどうか。false のときは innermost at 1 のみ行う。
     use_symmetry, l2rs はタクティクの評価前に列挙できる。ats は（少なくとも現状は）実行するまで何パターンあるかわからない。
     よって use_symmetry, l2rs は tclOR で列挙し、ats は証明時のエラーを補足して tclIFCATCH で列挙する。 *)
  let tcl use_symmetry l2rs full = (* [tcl use_symmetry l2rs] は引数のパラメータを使って、全ての [ats] に対して証明を試す。 *)
    let ats_length = List.length rewriters in
    (* let tclCONCAT ls =
      List.fold_left (fun acc next -> Proofview.tclTHEN acc next) Proofview.(tclUNIT ()) ls in *)
    let tclREWRITE_ALL ats = (* [tclREWRITE_ALL ats] rewrites H with given params. *)
      let rec aux rewriters ats l2rs i = match rewriters, ats, l2rs with
      | rewriter::rewriters, at::ats, l2r::l2rs ->
          Proofview.tclIFCATCH
            (let c = (fun env sigma ->
              (sigma,
                ( EConstr.mkRef (Nametab.global rewriter, EConstr.EInstance.empty),
                  Tactypes.NoBindings ) )) in
              rewrite c at l2r)
            (fun _ -> aux rewriters ats l2rs (i + 1))
            (fun (ex, _) -> Proofview.tclZERO (RewriteFailAt i))
      | [], [], [] -> Proofview.tclUNIT ()
      | _, _, _ -> failwith "tclREWRITE_ALL: Inconsistent length rewriters vs ats vs l2rs" in
      aux rewriters ats l2rs 0 in

    let tclREWRITE_ALL_INNERMOST =
      let rec aux rewriters l2rs i = match rewriters, l2rs with
      | rewriter::rewriters, l2r::l2rs ->
          Proofview.tclIFCATCH
            (cl_rewrite_clause_innermost rewriter l2r)
            (fun _ -> aux rewriters l2rs (i + 1))
            (fun (ex, _) -> Proofview.tclZERO (RewriteFailAt i))
      | [], [] -> Proofview.tclUNIT ()
      | _, _ -> failwith "tclREWRITE_ALL_INNERMOST: Inconsistent length rewriters vs ats vs l2rs" in
      aux rewriters l2rs 0 in

    let tclSINGLE_STEP tclREWRITE_ALL = (* [tclSINGLE_STEP tclREWRITE_ALL] tries proving with given tactic [tclREWRITE_ALL]. *)
      let open Proofview.Notations in
      Tactics.intros <*>
      Tactics.pose_proof (Names.Name (Names.Id.of_string "H")) (EConstr.mkRef (Nametab.global rewritee, EConstr.EInstance.empty)) <*>
      tclREWRITE_ALL <*>
      (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC) <*>
      (* HACK: G -> a = b の形の解決のために、型 G を持つ Parameter を Resolve Hint にもつ HintDb を追加しておく必要がある. *)
      Auto.default_full_auto <*>
      (* Check if goal is cleared *)
      Proofview.numgoals >>= (function
        | 0 -> Proofview.tclUNIT ()
        | _ -> Proofview.tclZERO Prove_failed)
    in
    let rec ones_like = function
      | _ :: t -> 1 :: ones_like t
      | [] -> [] in
    let rec inc_at ls i =
      if i < 0 then failwith "inc_at: Invalid argument" else
      match ls with
      | h :: t -> if i = 0 then (h + 1) :: ones_like t else h :: (inc_at t (i - 1))
      | [] -> failwith "inc_at: Invalid argument" in
    let rec aux ats =
      Proofview.tclIFCATCH
        (tclSINGLE_STEP (tclREWRITE_ALL ats))
        (fun _ -> Proofview.tclUNIT ())
        (fun (exn,_) ->
          match exn with
          | RewriteFailAt i -> if i = 0 then Proofview.tclZERO Prove_failed else aux (inc_at ats (i - 1))
          | _ -> aux (inc_at ats (ats_length - 1)))
      in
    if full then
      aux (List.init ats_length (fun _ -> 1))
    else
      tclSINGLE_STEP tclREWRITE_ALL_INNERMOST in
  let binlss =
    let rec aux l acc =
      match Devutil.next_binls l with
      | None -> acc
      | Some l -> aux l (l :: acc) in
    aux (List.init (1 + List.length rewriters) (fun _ -> true)) [(List.init (1 + List.length rewriters) (fun _ -> true))] in

  (* HACK: coq の rewrite.mli の都合上、innermost で at n を適用する書き換えが難しい。
     しかし多くのケースでは Innermost の at 1 が正しい書換になる。このため、最初に Innermost による書換を試し、その後全通りを試す。*)
  (* 全探索の方 *)
  let iter_all_patterns = List.fold_left (fun acc ls ->
      Proofview.tclIFCATCH (tcl (List.hd ls) (List.tl ls) true) (fun _ -> Proofview.tclUNIT ()) (fun _ -> acc)
    ) Proofview.(tclUNIT ()) binlss in
  (* innermost. こちらが先に実行されることに注意。 *)
  List.fold_left (fun acc ls ->
    Proofview.tclIFCATCH (tcl (List.hd ls) (List.tl ls) false) (fun _ -> Proofview.tclUNIT ()) (fun _ -> acc)
  ) iter_all_patterns binlss

      
(** 現在のゴールを冗長な規則の書換によって示す。 *)
let tac_prove_by_reduction ~(rewriters : Libnames.qualid list)
    ~(rewritee : Libnames.qualid) ~(l2rs : bool list) =
  let open Proofview.Notations in
  (*
    項の左右方向に関わらず証明するため、N個の書き換え規則に対して、l2rs として N+1 個のboolの組み合わせを受け取る。
    l2rs[0]  : symmetry. を使用するかどうか
    l2rs[1:] : i個目の cl_rewrite_clause の書き換え方向を -> にするかどうかを l2rs[i] で表す。
    term の形を調べるかtomaの出力を修正すれば事前に書き換え方向は決定できそうだが、実装の簡単のため全ての組み合わせを試す。
   *)
  let use_symmetry = List.hd l2rs in
  let l2rs = List.tl l2rs in
  Tactics.intros
  <*> Tactics.pose_proof
        (Names.Name (Names.Id.of_string "H"))
        (EConstr.mkRef (Nametab.global rewritee, EConstr.EInstance.empty))
  <*> List.fold_left
        (fun prev cur -> prev <*> cur)
        Tacticals.tclIDTAC
        (List.map
           (fun (rewriter, l2r) -> cl_rewrite_clause_innermost rewriter l2r)
           (List.combine rewriters l2rs))
  <*> (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC)
  <*> (* HACK: G -> a = b の形の解決のために、型 G を持つ Parameter を Resolve Hint にもつ HintDb を追加しておく必要がある. *)
  Auto.default_full_auto

let prove_interreduce ~(name : Names.Id.t)
    ~(* 証明する定理名 *)
    (goal : Constrexpr.constr_expr)
    ~(* 定理の型 *)
    (rewriters : Libnames.qualid list) ~(applier : Libnames.qualid) =
  (* apply を行う定理名 *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, body = Constrintern.interp_constr_evars env sigma goal in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let t, types, ustate, obl_info =
    Declare.Obls.prepare_obligation ~name ~types:None ~body sigma
  in
  let rec aux l2rs : unit =
    let tactic = tac_prove_by_reduction ~rewriters ~rewritee:applier ~l2rs in
    (* Suppress warning. It is ok because any proof that does not work will received as not successful. *)
    let tactic =
      Tacticals.tclIFCATCH tactic
        (fun () -> Proofview.tclUNIT ())
        (fun _ -> Proofview.tclUNIT ())
    in
    let _, progress =
      try
        Declare.Obls.add_definition ~pm:Declare.OblState.empty ~cinfo ~info
          ~uctx:ustate ~tactic obl_info
      with _ ->
        print_endline "GOT ERR";
        Declare.Obls.add_definition ~pm:Declare.OblState.empty ~cinfo ~info
          ~uctx:ustate ~tactic obl_info
    in
    match progress with
    | Defined _ -> ()
    | _ -> (
        match Devutil.next_binls l2rs with
        | None -> failwith "Could not prove goal by reduction."
        | Some l2rs -> aux l2rs)
  in
  aux (List.init (List.length rewriters + 1) (fun _ -> true))

let tclPROVE_INTERREDUCE ~(name : Names.Id.t)
    ~(* 証明する定理名 *)
    (goal : Constrexpr.constr_expr)
    ~(* 定理の型 *)
    (rewriters : Libnames.qualid list) ~(applier : Libnames.qualid) =
  (* apply を行う定理名 *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, body = Constrintern.interp_constr_evars env sigma goal in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let t, types, ustate, obl_info =
    Declare.Obls.prepare_obligation ~name ~types:None ~body sigma
  in
  let tactic = tclPROVE_BY_REDUCTION ~name ~goal ~rewritee:applier ~rewriters in
  let _, progress =
      Declare.Obls.add_definition ~pm:Declare.OblState.empty ~cinfo ~info
        ~uctx:ustate ~tactic obl_info in
  match progress with
  | Defined _ -> ()
  | _ -> failwith "Could not prove goal by reduction."

(** [Complete ... for S] の S に当たる、完備化のゴールを証明する。
    与えられた規則のリストで簡約すると両辺が等しくなることから示す。*)
let prove_completion_subject ~(name : Names.Id.t)
  ~(goal : Constrexpr.constr_expr)
  ~(rewriters : Libnames.qualid list) =

  let rewrite c at l2r =
    cl_rewrite_clause c l2r (OnlyOccurrences [ at ]) None in
  let ats_length = List.length rewriters in

  let tcl l2rs full = (* [tcl l2rs full] は引数のパラメータを使って、全ての [ats] に対して証明を試す。
    full=false のとき、innermost で ats=[1;1;...;1] の実行をする。これは高速で、多くの場合これで成功する。 *)
    let tclREWRITE_ALL ats = (* [tclREWRITE_ALL ats] rewrites H with given params. *)
      let rec aux rewriters ats l2rs i = match rewriters, ats, l2rs with
      | rewriter::rewriters, at::ats, l2r::l2rs ->
          Proofview.tclIFCATCH
            (let c = (fun env sigma ->
              ( sigma,
                ( EConstr.mkRef (Nametab.global rewriter, EConstr.EInstance.empty),
                  Tactypes.NoBindings ) )) in
              rewrite c at l2r)
            (fun _ -> aux rewriters ats l2rs (i + 1))
            (fun (ex, _) -> Proofview.tclZERO (RewriteFailAt i))
      | [], [], [] -> Proofview.tclUNIT ()
      | _, _, _ -> failwith "tclREWRITE_ALL: Inconsistent length rewriters vs ats vs l2rs" in
      aux rewriters ats l2rs 0 in

    let tclREWRITE_ALL_INNERMOST =
      let rec aux rewriters l2rs i = match rewriters, l2rs with
      | rewriter::rewriters, l2r::l2rs ->
          Proofview.tclIFCATCH
            (cl_rewrite_clause_innermost rewriter l2r)
            (fun _ -> aux rewriters l2rs (i + 1))
            (fun (ex, _) -> Proofview.tclZERO (RewriteFailAt i))
      | [], [] -> Proofview.tclUNIT ()
      | _, _ -> failwith "tclREWRITE_ALL_INNERMOST: Inconsistent length rewriters vs ats vs l2rs" in
      aux rewriters l2rs 0 in


    let tclSINGLE_STEP tclREWRITE_ALL = (* [tclSINGLE_STEP ats] tries proving with given tactic [tclREWRITE_ALL]. *)
      let open Proofview.Notations in
      Tactics.intros <*>
      tclREWRITE_ALL <*>

      (* HACK: G -> a = b の形の解決のために、型 G を持つ Parameter を Resolve Hint にもつ HintDb を追加しておく必要がある. *)
      (* reflexivity だけでも良いかも *)
      Auto.default_full_auto <*>

      (* Check if goal is cleared *)
      Proofview.numgoals >>= (function
        | 0 -> Proofview.tclUNIT ()
        | _ -> Proofview.tclZERO Prove_failed)
    in
    let rec ones_like = function
      | _ :: t -> 1 :: ones_like t
      | [] -> [] in
    let rec inc_at ls i =
      if i < 0 then failwith "inc_at: Invalid argument" else
      match ls with
      | h :: t -> if i = 0 then (h + 1) :: ones_like t else h :: (inc_at t (i - 1))
      | [] -> failwith "inc_at: Invalid argument" in
    let rec aux ats =
      Proofview.tclIFCATCH
        (tclSINGLE_STEP (tclREWRITE_ALL ats))
        (fun _ -> Proofview.tclUNIT ())
        (fun (exn,_) ->
          match exn with
          | RewriteFailAt i -> if i = 0 then Proofview.tclZERO Prove_failed else aux (inc_at ats (i - 1))
          | _ -> aux (inc_at ats (ats_length - 1)))
      in
    if full then
      aux (List.init ats_length (fun _ -> 1))
    else tclSINGLE_STEP tclREWRITE_ALL_INNERMOST in
  let binlss =
    let rec aux l acc =
      match Devutil.next_binls l with
      | None -> acc
      | Some l -> aux l (l :: acc) in
    aux (List.init ats_length (fun _ -> true)) [(List.init ats_length (fun _ -> true))] in
  let tactic =
    let tactic_full =
      List.fold_left (fun acc ls ->
        Proofview.tclIFCATCH (tcl ls true) (fun _ -> Proofview.tclUNIT ()) (fun _ -> acc)
      ) Proofview.(tclUNIT ()) binlss in
    (* innermost. Notice that this runs earlier before [tactic_full] *)
    List.fold_left (fun acc ls ->
      Proofview.tclIFCATCH (tcl ls false) (fun _ -> Proofview.tclUNIT ()) (fun _ -> acc)
    ) tactic_full binlss in


  (* Definition *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, body = Constrintern.interp_constr_evars env sigma goal in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let t, types, ustate, obl_info =
    Declare.Obls.prepare_obligation ~name ~types:None ~body sigma
  in
  let _, progress =
      Declare.Obls.add_definition ~pm:Declare.OblState.empty ~cinfo ~info
        ~uctx:ustate ~tactic obl_info in
  match progress with
  | Defined _ -> ()
  | _ -> failwith "Could not prove goal by reduction."

