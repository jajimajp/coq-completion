open My_term

type termid = string

(* 規則の番号, 左辺, 右辺 *)
type tomarule = termid * term * term

type tomaoutputsection =
  (* 公理のリスト 最初に与えた規則を表示するが、定理のIDや左辺・右辺の順は異なっている可能性がある *)
| Axioms of tomarule list
  (* 新しい規則, 簡約規則のリスト *)
| ReductionOrder of tomarule list
  (* 新しい規則, criticalpairs の規則１、規則２、superposition *)
| CriticalPairs of (tomarule * termid * termid * term) list
  (* 規則1, 規則2, 書換に使った規則のリスト - 規則１をinterreduceして規則２を得る *)
| Interreduce of (tomarule * tomarule * termid list) list
  (* 最終的な規則一覧 *)
| TerminationSuccess of tomarule list

val describe_toma_output : string list -> unit

val readtomaoutput : string list -> tomaoutputsection list
