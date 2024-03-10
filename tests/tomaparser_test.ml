open Plugin.Tomaparser

let input = {|
Completed
axioms:
0: +(0(), X0) = X0.
1: +(-(X1), X1) = 0().
2: +(+(X1, X0), X2) = +(X1, +(X0, X2)).
generated rules:
0: +(0(), X0) -> X0.
Proof: Axiom.

1: +(-(X1), X1) -> 0().
Proof: Axiom.

2: +(+(X1, X0), X2) -> +(X1, +(X0, X2)).
Proof: Axiom.

3: +(-(X3), +(X3, X2)) -> +(0(), X2).
Proof: A critical pair between equations 2 and 1 with superposition +(+(-(X3), X3), X2).

4: +(-(X3), +(X3, X2)) -> X2.
Proof: Rewrite equation 3,
              lhs with equations []
              rhs with equations [0].

5: X4 <- +(-(0()), X4).
Proof: A critical pair between equations 4 and 0 with superposition +(-(0()), +(0(), X4)).

6: X4 <- +(-(-(X4)), 0()).
Proof: A critical pair between equations 4 and 1 with superposition +(-(-(X4)), +(-(X4), X4)).

7: +(X4, X5) <- +(-(-(X4)), X5).
Proof: A critical pair between equations 4 and 4 with superposition +(-(-(X4)), +(-(X4), +(X4, X5))).

8: X6 <- +(-(+(X4, X5)), +(X4, +(X5, X6))).
Proof: A critical pair between equations 4 and 2 with superposition +(-(+(X4, X5)), +(+(X4, X5), X6)).

9: X4 <- +(X4, 0()).
Proof: Rewrite equation 6,
              lhs with equations []
              rhs with equations [7].

10: -(0()) -> 0().
Proof: A critical pair between equations 9 and 5 with superposition +(-(0()), 0()).

11: +(X4, -(X4)) -> 0().
Proof: A critical pair between equations 7 and 1 with superposition +(-(-(X4)), -(X4)).

12: +(X4, 0()) <- -(-(X4)).
Proof: A critical pair between equations 7 and 9 with superposition +(-(-(X4)), 0()).

13: X4 <- +(-(-(X4)), 0()).
Proof: A critical pair between equations 4 and 1 with superposition +(-(-(X4)), +(-(X4), X4)).

14: +(X4, +(-(X4), X7)) -> X7.
Proof: A critical pair between equations 7 and 4 with superposition +(-(-(X4)), +(-(X4), X7)).

15: X7 <- +(-(+(X4, -(0()))), +(X4, X7)).
Proof: A critical pair between equations 8 and 5 with superposition +(-(+(X4, -(0()))), +(X4, +(-(0()), X7))).

16: X7 <- +(-(+(X4, -(X7))), +(X4, 0())).
Proof: A critical pair between equations 8 and 1 with superposition +(-(+(X4, -(X7))), +(X4, +(-(X7), X7))).

17: X6 <- +(-(+(-(+(X5, X6)), X5)), 0()).
Proof: A critical pair between equations 8 and 1 with superposition +(-(+(-(+(X5, X6)), X5)), +(-(+(X5, X6)), +(X5, X6))).

18: +(X8, X9) <- +(-(+(-(+(X7, X8)), X7)), X9).
Proof: A critical pair between equations 8 and 8 with superposition +(-(+(-(+(X7, X8)), X7)), +(-(+(X7, X8)), +(X7, +(X8, X9)))).

19: +(X7, X8) <- +(-(+(X4, -(X7))), +(X4, X8)).
Proof: A critical pair between equations 8 and 4 with superposition +(-(+(X4, -(X7))), +(X4, +(-(X7), +(X7, X8)))).

20: X8 <- +(-(+(X4, -(-(X7)))), +(X4, +(X7, X8))).
Proof: A critical pair between equations 8 and 7 with superposition +(-(+(X4, -(-(X7)))), +(X4, +(-(-(X7)), X8))).

21: X9 <- +(-(+(X4, +(X7, X8))), +(X4, +(X7, +(X8, X9)))).
Proof: A critical pair between equations 8 and 2 with superposition +(-(+(X4, +(X7, X8))), +(X4, +(+(X7, X8), X9))).

22: X6 <- -(+(-(+(X5, X6)), X5)).
Proof: Rewrite equation 17,
              lhs with equations []
              rhs with equations [9].

23: X7 <- +(-(+(X4, -(X7))), X4).
Proof: Rewrite equation 16,
              lhs with equations []
              rhs with equations [9].

24: X4 <- -(-(X4)).
Proof: Rewrite equation 12,
              lhs with equations [9]
              rhs with equations [].

25: +(X8, -(+(-(X11), X8))) -> X11.
Proof: A critical pair between equations 18 and 23 with superposition +(-(+(-(+(-(X11), X8)), -(X11))), -(+(-(X11), X8))).

26: X10 <- -(+(X11, -(+(X10, X11)))).
Proof: A critical pair between equations 22 and 18 with superposition -(+(-(+(-(+(X10, X11)), X10)), -(+(X10, X11)))).

27: -(X8) <- +(-(+(X4, X8)), X4).
Proof: A critical pair between equations 23 and 24 with superposition +(-(+(X4, -(-(X8)))), X4).

28: +(X8, +(-(+(X7, X8)), X7)) -> 0().
Proof: A critical pair between equations 18 and 1 with superposition +(-(+(-(+(X7, X8)), X7)), +(-(+(X7, X8)), X7)).

29: +(-(X8), X9) <- -(+(-(X9), X8)).
Proof: A critical pair between equations 22 and 14 with superposition -(+(-(+(X8, +(-(X8), X9))), X8)).

30: +(X7, X8) <- -(+(-(X8), -(X7))).
Proof: A critical pair between equations 22 and 4 with superposition -(+(-(+(-(X7), +(X7, X8))), -(X7))).

31: 0() <- +(X5, +(X6, -(+(X5, X6)))).
Proof: A critical pair between equations 11 and 2 with superposition +(+(X5, X6), -(+(X5, X6))).

32: X8 <- -(+(-(X9), -(+(X8, -(X9))))).
Proof: A critical pair between equations 22 and 23 with superposition -(+(-(+(-(+(X8, -(X9))), X8)), -(+(X8, -(X9))))).

33: X7 <- +(-(X9), -(+(-(X7), -(X9)))).
Proof: A critical pair between equations 23 and 23 with superposition +(-(+(-(+(-(X7), -(X9))), -(X7))), -(+(-(X7), -(X9)))).

34: -(X7) <- +(-(+(X4, X7)), +(X4, 0())).
Proof: A critical pair between equations 8 and 11 with superposition +(-(+(X4, X7)), +(X4, +(X7, -(X7)))).

35: +(X7, -(X9)) <- +(-(+(X9, -(X7))), 0()).
Proof: A critical pair between equations 19 and 11 with superposition +(-(+(X9, -(X7))), +(X9, -(X9))).

36: +(X7, X9) <- +(-(+(-(X9), -(X7))), 0()).
Proof: A critical pair between equations 19 and 1 with superposition +(-(+(-(X9), -(X7))), +(-(X9), X9)).

37: +(X7, -(X9)) <- -(+(X9, -(X7))).
Proof: Rewrite equation 35,
              lhs with equations []
              rhs with equations [9].

38: +(-(X10), -(X9)) <- -(+(X9, X10)).
Proof: A critical pair between equations 37 and 24 with superposition -(+(X9, -(-(X10)))).

39: -(X9) <- +(-(-(X10)), -(+(X9, X10))).
Proof: A critical pair between equations 27 and 27 with superposition +(-(+(-(+(X9, X10)), X9)), -(+(X9, X10))).

40: +(X8, -(+(X7, X8))) -> +(-(X7), 0()).
Proof: A critical pair between equations 4 and 31 with superposition +(-(X7), +(X7, +(X8, -(+(X7, X8))))).

41: +(X1, +(X0, +(-(+(X1, X0)), X9))) -> X9.
Proof: A critical pair between equations 2 and 14 with superposition +(+(X1, X0), +(-(+(X1, X0)), X9)).

42: +(-(+(X10, +(X11, X12))), +(X10, X11)) -> -(X12).
Proof: A critical pair between equations 29 and 8 with superposition -(+(-(+(X10, X11)), +(X10, +(X11, X12)))).

43: +(-(X8), X9) <- +(-(+(X4, X8)), +(X4, X9)).
Proof: A critical pair between equations 8 and 14 with superposition +(-(+(X4, X8)), +(X4, +(X8, +(-(X8), X9)))).

44: +(X7, -(+(X10, X11))) <- -(+(X10, +(X11, -(X7)))).
Proof: A critical pair between equations 37 and 2 with superposition -(+(+(X10, X11), -(X7))).

45: 0() <- +(+(X7, X8), +(X9, -(+(X7, +(X8, X9))))).
Proof: A critical pair between equations 31 and 2 with superposition +(+(X7, X8), +(X9, -(+(+(X7, X8), X9)))).

46: 0() <- +(X5, +(X7, +(X8, -(+(X5, +(X7, X8)))))).
Proof: A critical pair between equations 31 and 2 with superposition +(X5, +(+(X7, X8), -(+(X5, +(X7, X8))))).

47: 0() <- +(X7, +(X8, +(X6, -(+(+(X7, X8), X6))))).
Proof: A critical pair between equations 31 and 2 with superposition +(+(X7, X8), +(X6, -(+(+(X7, X8), X6)))).

48: -(+(X9, +(X10, X11))) -> +(-(X11), -(+(X9, X10))).
Proof: A critical pair between equations 27 and 8 with superposition +(-(+(-(+(X9, X10)), +(X9, +(X10, X11)))), -(+(X9, X10))).

49: X6 <- +(-(-(X10)), +(-(+(X9, X10)), +(X9, X6))).
Proof: A critical pair between equations 8 and 27 with superposition +(-(+(-(+(X9, X10)), X9)), +(-(+(X9, X10)), +(X9, X6))).

ES:
9: +(X4, 0()) -> X4
0: +(0(), X0) -> X0
1: +(-(X1), X1) -> 0()
2: +(+(X1, X0), X2) -> +(X1, +(X0, X2))
4: +(-(X3), +(X3, X2)) -> X2
10: -(0()) -> 0()
11: +(X4, -(X4)) -> 0()
24: -(-(X4)) -> X4
14: +(X4, +(-(X4), X7)) -> X7
38: -(+(X9, X10)) -> +(-(X10), -(X9))
|} |> String.split_on_char '\n'

let%expect_test "parse" =
  V6.print_procedure (V6.parse input);
  [%expect {|
   Axiom: 0: +(0,X0) -> X0
   Axiom: 1: +(-(X1),X1) -> 0
   Axiom: 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2))
   Crit: 3: +(-(X3),+(X3,X2)) -> +(0,X2) with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 1: +(-(X1),X1) -> 0 with superposition +(+(-(X3),X3),X2)
   Simp: 4: +(-(X3),+(X3,X2)) -> X2 with 0
   Crit: 5: +(-(0),X4) -> X4 with 0: +(0,X0) -> X0 and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(0),+(0,X4))
   Crit: 6: +(-(-(X4)),0) -> X4 with 1: +(-(X1),X1) -> 0 and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(-(X4)),+(-(X4),X4))
   Crit: 7: +(-(-(X4)),X5) -> +(X4,X5) with 4: +(-(X3),+(X3,X2)) -> X2 and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(-(X4)),+(-(X4),+(X4,X5)))
   Crit: 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(+(X4,X5)),+(+(X4,X5),X6))
   Simp: 9: +(X4,0) -> X4 with 7
   Crit: 10: -(0) -> 0 with 9: +(X4,0) -> X4 and 5: +(-(0),X4) -> X4 with superposition +(-(0),0)
   Crit: 11: +(X4,-(X4)) -> 0 with 7: +(-(-(X4)),X5) -> +(X4,X5) and 1: +(-(X1),X1) -> 0 with superposition +(-(-(X4)),-(X4))
   Crit: 12: -(-(X4)) -> +(X4,0) with 9: +(X4,0) -> X4 and 7: +(-(-(X4)),X5) -> +(X4,X5) with superposition +(-(-(X4)),0)
   Crit: 13: +(-(-(X4)),0) -> X4 with 1: +(-(X1),X1) -> 0 and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(-(X4)),+(-(X4),X4))
   Crit: 14: +(X4,+(-(X4),X7)) -> X7 with 7: +(-(-(X4)),X5) -> +(X4,X5) and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(-(X4)),+(-(X4),X7))
   Crit: 15: +(-(+(X4,-(0))),+(X4,X7)) -> X7 with 5: +(-(0),X4) -> X4 and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(X4,-(0))),+(X4,+(-(0),X7)))
   Crit: 16: +(-(+(X4,-(X7))),+(X4,0)) -> X7 with 1: +(-(X1),X1) -> 0 and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(X4,-(X7))),+(X4,+(-(X7),X7)))
   Crit: 17: +(-(+(-(+(X5,X6)),X5)),0) -> X6 with 1: +(-(X1),X1) -> 0 and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(-(+(X5,X6)),X5)),+(-(+(X5,X6)),+(X5,X6)))
   Crit: 18: +(-(+(-(+(X7,X8)),X7)),X9) -> +(X8,X9) with 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(-(+(X7,X8)),X7)),+(-(+(X7,X8)),+(X7,+(X8,X9))))
   Crit: 19: +(-(+(X4,-(X7))),+(X4,X8)) -> +(X7,X8) with 4: +(-(X3),+(X3,X2)) -> X2 and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(X4,-(X7))),+(X4,+(-(X7),+(X7,X8))))
   Crit: 20: +(-(+(X4,-(-(X7)))),+(X4,+(X7,X8))) -> X8 with 7: +(-(-(X4)),X5) -> +(X4,X5) and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(X4,-(-(X7)))),+(X4,+(-(-(X7)),X8)))
   Crit: 21: +(-(+(X4,+(X7,X8))),+(X4,+(X7,+(X8,X9)))) -> X9 with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(X4,+(X7,X8))),+(X4,+(+(X7,X8),X9)))
   Simp: 22: -(+(-(+(X5,X6)),X5)) -> X6 with 9
   Simp: 23: +(-(+(X4,-(X7))),X4) -> X7 with 9
   Simp: 24: -(-(X4)) -> X4 with 9
   Crit: 25: +(X8,-(+(-(X11),X8))) -> X11 with 18: +(-(+(-(+(X7,X8)),X7)),X9) -> +(X8,X9) and 23: +(-(+(X4,-(X7))),X4) -> X7 with superposition +(-(+(-(+(-(X11),X8)),-(X11))),-(+(-(X11),X8)))
   Crit: 26: -(+(X11,-(+(X10,X11)))) -> X10 with 18: +(-(+(-(+(X7,X8)),X7)),X9) -> +(X8,X9) and 22: -(+(-(+(X5,X6)),X5)) -> X6 with superposition -(+(-(+(-(+(X10,X11)),X10)),-(+(X10,X11))))
   Crit: 27: +(-(+(X4,X8)),X4) -> -(X8) with 24: -(-(X4)) -> X4 and 23: +(-(+(X4,-(X7))),X4) -> X7 with superposition +(-(+(X4,-(-(X8)))),X4)
   Crit: 28: +(X8,+(-(+(X7,X8)),X7)) -> 0 with 18: +(-(+(-(+(X7,X8)),X7)),X9) -> +(X8,X9) and 1: +(-(X1),X1) -> 0 with superposition +(-(+(-(+(X7,X8)),X7)),+(-(+(X7,X8)),X7))
   Crit: 29: -(+(-(X9),X8)) -> +(-(X8),X9) with 14: +(X4,+(-(X4),X7)) -> X7 and 22: -(+(-(+(X5,X6)),X5)) -> X6 with superposition -(+(-(+(X8,+(-(X8),X9))),X8))
   Crit: 30: -(+(-(X8),-(X7))) -> +(X7,X8) with 4: +(-(X3),+(X3,X2)) -> X2 and 22: -(+(-(+(X5,X6)),X5)) -> X6 with superposition -(+(-(+(-(X7),+(X7,X8))),-(X7)))
   Crit: 31: +(X5,+(X6,-(+(X5,X6)))) -> 0 with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 11: +(X4,-(X4)) -> 0 with superposition +(+(X5,X6),-(+(X5,X6)))
   Crit: 32: -(+(-(X9),-(+(X8,-(X9))))) -> X8 with 23: +(-(+(X4,-(X7))),X4) -> X7 and 22: -(+(-(+(X5,X6)),X5)) -> X6 with superposition -(+(-(+(-(+(X8,-(X9))),X8)),-(+(X8,-(X9)))))
   Crit: 33: +(-(X9),-(+(-(X7),-(X9)))) -> X7 with 23: +(-(+(X4,-(X7))),X4) -> X7 and 23: +(-(+(X4,-(X7))),X4) -> X7 with superposition +(-(+(-(+(-(X7),-(X9))),-(X7))),-(+(-(X7),-(X9))))
   Crit: 34: +(-(+(X4,X7)),+(X4,0)) -> -(X7) with 11: +(X4,-(X4)) -> 0 and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(X4,X7)),+(X4,+(X7,-(X7))))
   Crit: 35: +(-(+(X9,-(X7))),0) -> +(X7,-(X9)) with 11: +(X4,-(X4)) -> 0 and 19: +(-(+(X4,-(X7))),+(X4,X8)) -> +(X7,X8) with superposition +(-(+(X9,-(X7))),+(X9,-(X9)))
   Crit: 36: +(-(+(-(X9),-(X7))),0) -> +(X7,X9) with 1: +(-(X1),X1) -> 0 and 19: +(-(+(X4,-(X7))),+(X4,X8)) -> +(X7,X8) with superposition +(-(+(-(X9),-(X7))),+(-(X9),X9))
   Simp: 37: -(+(X9,-(X7))) -> +(X7,-(X9)) with 9
   Crit: 38: -(+(X9,X10)) -> +(-(X10),-(X9)) with 24: -(-(X4)) -> X4 and 37: -(+(X9,-(X7))) -> +(X7,-(X9)) with superposition -(+(X9,-(-(X10))))
   Crit: 39: +(-(-(X10)),-(+(X9,X10))) -> -(X9) with 27: +(-(+(X4,X8)),X4) -> -(X8) and 27: +(-(+(X4,X8)),X4) -> -(X8) with superposition +(-(+(-(+(X9,X10)),X9)),-(+(X9,X10)))
   Crit: 40: +(X8,-(+(X7,X8))) -> +(-(X7),0) with 4: +(-(X3),+(X3,X2)) -> X2 and 31: +(X5,+(X6,-(+(X5,X6)))) -> 0 with superposition +(-(X7),+(X7,+(X8,-(+(X7,X8)))))
   Crit: 41: +(X1,+(X0,+(-(+(X1,X0)),X9))) -> X9 with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 14: +(X4,+(-(X4),X7)) -> X7 with superposition +(+(X1,X0),+(-(+(X1,X0)),X9))
   Crit: 42: +(-(+(X10,+(X11,X12))),+(X10,X11)) -> -(X12) with 29: -(+(-(X9),X8)) -> +(-(X8),X9) and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition -(+(-(+(X10,X11)),+(X10,+(X11,X12))))
   Crit: 43: +(-(+(X4,X8)),+(X4,X9)) -> +(-(X8),X9) with 14: +(X4,+(-(X4),X7)) -> X7 and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(X4,X8)),+(X4,+(X8,+(-(X8),X9))))
   Crit: 44: -(+(X10,+(X11,-(X7)))) -> +(X7,-(+(X10,X11))) with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 37: -(+(X9,-(X7))) -> +(X7,-(X9)) with superposition -(+(+(X10,X11),-(X7)))
   Crit: 45: +(+(X7,X8),+(X9,-(+(X7,+(X8,X9))))) -> 0 with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 31: +(X5,+(X6,-(+(X5,X6)))) -> 0 with superposition +(+(X7,X8),+(X9,-(+(+(X7,X8),X9))))
   Crit: 46: +(X5,+(X7,+(X8,-(+(X5,+(X7,X8)))))) -> 0 with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 31: +(X5,+(X6,-(+(X5,X6)))) -> 0 with superposition +(X5,+(+(X7,X8),-(+(X5,+(X7,X8)))))
   Crit: 47: +(X7,+(X8,+(X6,-(+(+(X7,X8),X6))))) -> 0 with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 31: +(X5,+(X6,-(+(X5,X6)))) -> 0 with superposition +(+(X7,X8),+(X6,-(+(+(X7,X8),X6))))
   Crit: 48: -(+(X9,+(X10,X11))) -> +(-(X11),-(+(X9,X10))) with 27: +(-(+(X4,X8)),X4) -> -(X8) and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(-(+(X9,X10)),+(X9,+(X10,X11)))),-(+(X9,X10)))
   Crit: 49: +(-(-(X10)),+(-(+(X9,X10)),+(X9,X6))) -> X6 with 27: +(-(+(X4,X8)),X4) -> -(X8) and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(-(+(X9,X10)),X9)),+(-(+(X9,X10)),+(X9,X6)))
   Completed: 9: +(X4,0) -> X4
   Completed: 0: +(0,X0) -> X0
   Completed: 1: +(-(X1),X1) -> 0
   Completed: 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2))
   Completed: 4: +(-(X3),+(X3,X2)) -> X2
   Completed: 10: -(0) -> 0
   Completed: 11: +(X4,-(X4)) -> 0
   Completed: 24: -(-(X4)) -> X4
   Completed: 14: +(X4,+(-(X4),X7)) -> X7
   Completed: 38: -(+(X9,X10)) -> +(-(X10),-(X9))
    |}]