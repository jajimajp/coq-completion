val complete :
  axioms: Libnames.qualid list -> (* 公理名のリスト *)
    hint_db_name: string -> (* 完備化された定理が登録されるヒントDBの名前 *)
      ops: Libnames.qualid list (* 関数名のリスト 引数0個の定数も含む *) ->
        string list (* 出力のリスト *)