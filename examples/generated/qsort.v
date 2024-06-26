(*
This example was automatically generated by converting from
qsort.trs: 

(VAR x y m n)
(RULES
le(0, y) -> true
le(s(x), 0) -> false
le(s(x), s(y)) -> le(x, y)
app(nil, y) -> y
app(add(n,x),y) -> add(n, app(x,y))
low(n, nil) -> nil
low(n, cons(m, x)) -> if_low(le(m,n), n, add(m,x))
if_low(true,n,add(m,x)) -> add(m,low(n,x))
if_low(false,n,add(m,x)) -> low(n,x)
high(n, nil) -> nil
high(n,add(m,x)) -> if_high(le(m,n),n,add(m,x))
if_high(true,n,add(m,x)) -> high(n,x)
if_high(false,n,add(m,x)) -> add(m, high(n,x))
quicksort(nil) -> nil
quicksort(add(n,x)) -> app(quicksort(low(n,x)), add(n, quicksort(high(n,x))))
)
(COMMENT
AG01 Example 3.11
)

*)

Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Parameter G : Set.
    
Parameter add : G -> G -> G.
Parameter app : G -> G -> G.
Parameter cons : G -> G -> G.
Parameter false : G.
Parameter high : G -> G -> G.
Parameter if_high : G -> G -> G -> G.
Parameter if_low : G -> G -> G -> G.
Parameter le : G -> G -> G.
Parameter low : G -> G -> G.
Parameter nil : G.
Parameter quicksort : G -> G.
Parameter s : G -> G.
Parameter true : G.
Parameter zero : G.
Axiom ax0 : forall n x, quicksort (add n x) = app (quicksort (low n x)) (add n (quicksort (high n x))).
Axiom ax1 : quicksort nil = nil.
Axiom ax2 : forall n m x, if_high false n (add m x) = add m (high n x).
Axiom ax3 : forall n m x, if_high true n (add m x) = high n x.
Axiom ax4 : forall n m x, high n (add m x) = if_high (le m n) n (add m x).
Axiom ax5 : forall n, high n nil = nil.
Axiom ax6 : forall n m x, if_low false n (add m x) = low n x.
Axiom ax7 : forall n m x, if_low true n (add m x) = add m (low n x).
Axiom ax8 : forall n m x, low n (cons m x) = if_low (le m n) n (add m x).
Axiom ax9 : forall n, low n nil = nil.
Axiom ax10 : forall n x y, app (add n x) y = add n (app x y).
Axiom ax11 : forall y, app nil y = y.
Axiom ax12 : forall x y, le (s x) (s y) = le x y.
Axiom ax13 : forall x, le (s x) zero = false.
Axiom ax14 : forall y, le zero y = true.
Create HintDb hint_compl.
Complete ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8 ax9 ax10 ax11 ax12 ax13 ax14 : add app cons false high if_high if_low le low nil quicksort s true zero : hint_compl.
Print Rewrite HintDb hint_compl.
