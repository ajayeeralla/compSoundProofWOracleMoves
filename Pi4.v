
Load "Pi3".

(******************************Protocol Pi2' :**************************************************************************)



Definition t40 := msg (G (N 0)).
Definition t41 := msg (g (N 0)).
Definition phi40 := [t40; t41].
Definition mphi40 := (conv_mylist_listm phi40).
Definition msgt40 := (ostomsg t40).
Definition msgt41 := (ostomsg t41).
Definition grn41 := (exp msgt40 msgt41 (r (N 1))).
Definition qd0000:= (if_then_else_M (EQ_M (reveal (f mphi40)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi40)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi40)) (i 1)) & (EQ_M (act (f mphi40)) new)) grn41 (if_then_else_M (EQ_M (to (f mphi40)) (i 1)) grn41 (if_then_else_M ((EQ_M (to (f mphi40)) (i 2)) & (EQ_M (act (f mphi40)) new)) grn41 (if_then_else_M (EQ_M (to (f mphi40)) (i 2)) grn41 O) ) )))).
Definition t42:= msg qc0000.
Definition phi41 := phi40 ++ [ t42 ].

 (***********************************************************)
(***********************************************************)
Definition msgt42:= (ostomsg t42).
Definition mphi41 := (conv_mylist_listm phi41).


Definition mx41rn1 := (exp msgt40 (m (f mphi40 )) (r (N 1))).
 Definition mx41rn2 := (exp msgt40 (m (f mphi40 )) (r (N 2))).

Definition grn42:= (exp msgt40 msgt41 (r (N 2))).


(**********qd0000 -> qd1000, qd0010, qd0100, qd0001*************************************************)

Definition qd1000 := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) acc (if_then_else_M ((EQ_M (to (f mphi41)) (i 2)) & (EQ_M (act (f mphi41)) new)) grn42 (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) grn42 O))))).

Definition qd0010:= (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi41)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1))) mx41rn1 (if_then_else_M ((EQ_M (to (f mphi41)) (i 2)) & (EQ_M (act (f mphi41)) new)) grn42 (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) grn42 O) ) ) ).

Definition qd0100 := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) acc (if_then_else_M ((EQ_M (to (f mphi41)) (i 1)) & (EQ_M (act (f mphi41)) new)) grn41 (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) grn41 O))))).

Definition qd0001 :=(if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi41)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1))) mx41rn1 (if_then_else_M ((EQ_M (to (f mphi41)) (i 1)) & (EQ_M (act (f mphi41)) new)) grn42 (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) grn42 O) ) ) ).

Definition t43 := msg (if_then_else_M (EQ_M (reveal (f mphi40)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi40)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi40)) (i 1)) & (EQ_M (act (f mphi40)) new)) qd1000 (if_then_else_M (EQ_M (to (f mphi40)) (i 1)) qd0010 (if_then_else_M ((EQ_M (to (f mphi40)) (i 2)) & (EQ_M (act (f mphi40)) new)) qd0100 (if_then_else_M (EQ_M (to (f mphi40)) (i 2)) qd0001 O) ) )))).
Definition phi42:= phi41 ++ [t43].

(***************************************************************************)
(***************************************************************************)
Definition msgt43:= (ostomsg t43).
Definition mphi42 := (conv_mylist_listm phi42).

Definition mx42rn1 := (exp msgt40 (m (f mphi41 )) (r (N 1))).
Definition mx42rn2 := (exp msgt40 (m (f mphi41 )) (r (N 2))).
Definition grn43:= (exp msgt40 msgt41 (r (N 3))).



(************* qd1000 -> qd2000, qd1100, qd1001*******************************************************)

Definition qd2000 :=  (if_then_else_M (EQ_M (reveal (f mphi42)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1)) &(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   mx42rn1 (if_then_else_M ((EQ_M (to (f mphi42)) (i 2)) & (EQ_M (act (f mphi42)) new)) grn43 (if_then_else_M (EQ_M (to (f mphi42)) (i 2)) grn43 O) ) ) ).


Definition qd1100 := (if_then_else_M (EQ_M (reveal (f mphi42)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi42)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi42)) (i 1)) acc (if_then_else_M ((EQ_M (to (f mphi42)) (i 2)) ) acc O) ))).
Definition qd1001 := (if_then_else_M (EQ_M (reveal (f mphi42)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 2) ) & (EQ_M (to (f mphi40)) (i 2)))  mx41rn1 (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 2) ) & (EQ_M (to (f mphi41)) (i 2))) mx42rn2  (if_then_else_M (EQ_M (to (f mphi42)) (i 1)) acc O)))).
(************qd0010 -> qd0020, qd0110, qd0011*********************************************************)

Definition qd0110 := (if_then_else_M (EQ_M (reveal (f mphi42)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1)))  mx41rn1 (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1))) mx42rn2  (if_then_else_M (EQ_M (to (f mphi42)) (i 2)) acc O)))).

(*****************qd0100 -> qd0200, qd1100, qd0110****************************************************)

Definition qd0200 :=  (if_then_else_M (EQ_M (reveal (f mphi42)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 2) ) & (EQ_M (to (f mphi41)) (i 2)) &(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   mx42rn1 (if_then_else_M ((EQ_M (to (f mphi42)) (i 1)) & (EQ_M (act (f mphi42)) new)) grn43 (if_then_else_M (EQ_M (to (f mphi42)) (i 1)) grn43 O) ) ) ).

(******************qd0001 -> qd0002, qd1001, qd0011****************************************************)

(*****************************************************************************************************)

Definition qd1000_s := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) qd2000 (if_then_else_M ((EQ_M (to (f mphi41)) (i 2)) & (EQ_M (act (f mphi41)) new)) qd1100 (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) qd1001 O))))).

Definition qd0010_s := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi41)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi41)) (i 2)) & (EQ_M (act (f mphi41)) new)) qd0110 (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) O O) ) ) ).

Definition qd0100_s := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) qd0200 (if_then_else_M ((EQ_M (to (f mphi41)) (i 1)) & (EQ_M (act (f mphi41)) new)) qd1100 (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) qd0110 O))))).

Definition qd0001_s := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi41)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi41)) (i 1)) & (EQ_M (act (f mphi41)) new)) qd1001 (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) O O) ) ) ).

Definition t44 := msg (if_then_else_M (EQ_M (reveal (f mphi40)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi40)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi40)) (i 1)) & (EQ_M (act (f mphi40)) new)) qd1000_s (if_then_else_M (EQ_M (to (f mphi40)) (i 1)) qd0010_s (if_then_else_M ((EQ_M (to (f mphi40)) (i 2)) & (EQ_M (act (f mphi40)) new)) qd0100_s (if_then_else_M (EQ_M (to (f mphi40)) (i 2)) qd0001_s O) ) )))).

Definition phi43:= phi42 ++ [t44].
(***********************************************************************************************)
Definition mx43rn2 := (exp msgt40 (m (f mphi42 )) (r (N 2))).
Definition mphi43 := (conv_mylist_listm phi43).

(********************qd2000 -> qd3000, qd2100, qd2001****************************************************)
Definition qd2100 := (if_then_else_M (EQ_M (reveal (f mphi43)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1)) &(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   mx42rn1 (if_then_else_M (EQ_M (to (f mphi43)) (i 2)) acc O ) )).
(**************************qd1100 -> qd2100, qd1200 *****************************************************)
Definition qd1200 := (if_then_else_M (EQ_M (reveal (f mphi43)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi41)) (i 2)) &(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   mx42rn1 (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi42)) (i 2)) &(EQ_M (to (f mphi41)) (i 2)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi41)) new))   mx43rn2 (if_then_else_M (EQ_M (to (f mphi43)) (i 1)) acc O)) ) ).
(**********Changes to the states qd2001, qd0210 in protocol2**************************************************)
(*Definition grn44:= (exp msgt40 msgt41 (r (N 4))).*)
Definition grn421 := (exp msgt40 (grn42) (r (N 1))).

Definition qd2001 := (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi42)) (i 1)) &(EQ_M (to (f mphi41)) (i 2))&(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi40)) new) &(EQ_M (m (f mphi41)) grn41) &(EQ_M (m (f mphi42)) grn12))   grn421 (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 1) ) & (EQ_M (to (f mphi42)) (i 1)) &(EQ_M (to (f mphi41)) (i 2))&(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi40)) new) &(EQ_M (m (f mphi41)) grn41) &(EQ_M (m (f mphi42)) grn12))   grn421 (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 1) ) & (EQ_M (to (f mphi42)) (i 1)) &(EQ_M (to (f mphi41)) (i 1)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi41)) new))   mx43rn2 O ))).
 
Definition qd0210 :=  (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 1) ) & (EQ_M (to (f mphi42)) (i 2)) &(EQ_M (to (f mphi41)) (i 1))&(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi40)) new) &(EQ_M (m (f mphi41)) grn41) &(EQ_M (m (f mphi42)) grn12))   grn421 (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi42)) (i 2)) &(EQ_M (to (f mphi41)) (i 1))&(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi40)) new) &(EQ_M (m (f mphi41)) grn41) &(EQ_M (m (f mphi42)) grn12))   grn421 (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi41)) (i 2)) &(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   mx42rn1 O ))).

(********************************************************************************************************)
Definition qd0120 := (if_then_else_M (EQ_M (reveal (f mphi43)) (i 1) ) O ( if_then_else_M (EQ_M (to (f mphi41)) (i 2)) grn43 O)).


(*****************************qd1001 -> qd1002, qd2001***************************************************)

Definition qd2000_s :=  (if_then_else_M (EQ_M (reveal (f mphi42)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1)) &(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new)) O (if_then_else_M ((EQ_M (to (f mphi42)) (i 2)) & (EQ_M (act (f mphi42)) new)) qd2100 (if_then_else_M (EQ_M (to (f mphi42)) (i 2)) qd2001 O) ) ) ).


Definition qd1100_s := (if_then_else_M (EQ_M (reveal (f mphi42)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi42)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi42)) (i 1)) qd2100 (if_then_else_M ((EQ_M (to (f mphi42)) (i 2)) ) qd1200 O) ))).
Definition qd1001_s := (if_then_else_M (EQ_M (reveal (f mphi42)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 2) ) & (EQ_M (to (f mphi40)) (i 2)))  O (if_then_else_M (EQ_M (to (f mphi42)) (i 1)) qd2001 O))).

Definition qd0110_s := (if_then_else_M (EQ_M (reveal (f mphi42)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1)))  qd0120 (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1))) qd0120  (if_then_else_M (EQ_M (to (f mphi42)) (i 2)) qd0210 O)))).

Definition qd0200_s :=  (if_then_else_M (EQ_M (reveal (f mphi42)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 2) ) & (EQ_M (to (f mphi41)) (i 2)) &(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   O (if_then_else_M ((EQ_M (to (f mphi42)) (i 1)) & (EQ_M (act (f mphi42)) new)) qd1200 (if_then_else_M (EQ_M (to (f mphi42)) (i 1)) qd0210 O) ) ) ).
(***********************************************************************************************************)


Definition qd1000_ss := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) qd2000_s (if_then_else_M ((EQ_M (to (f mphi41)) (i 2)) & (EQ_M (act (f mphi41)) new)) qd1100_s (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) qd1001_s O))))).

Definition qd0010_ss := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi41)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi41)) (i 2)) & (EQ_M (act (f mphi41)) new)) qd0110_s (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) O O) ) ) ).

Definition qd0100_ss := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) qd0200_s (if_then_else_M ((EQ_M (to (f mphi41)) (i 1)) & (EQ_M (act (f mphi41)) new)) qd1100_s (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) qd0110_s O))))).

Definition qd0001_ss := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi41)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi41)) (i 1)) & (EQ_M (act (f mphi41)) new)) qd1001_s (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) O O) ) ) ).

Definition t45 := msg (if_then_else_M (EQ_M (reveal (f mphi40)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi40)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi40)) (i 1)) & (EQ_M (act (f mphi40)) new)) qd1000_ss (if_then_else_M (EQ_M (to (f mphi40)) (i 1)) qd0010_ss (if_then_else_M ((EQ_M (to (f mphi40)) (i 2)) & (EQ_M (act (f mphi40)) new)) qd0100_ss (if_then_else_M (EQ_M (to (f mphi40)) (i 2)) qd0001_ss O) ) )))).

Definition phi44 :=  phi43 ++ [ t45 ]. 

(***********************************************************************************************************)
Definition mf4ph41rn3 := (exp msgt40 (m (f mphi43 )) (r (N 3))).
Definition mphi44 := (conv_mylist_listm phi44).

(********************qd2100 -> qd2200, qd3100************************************)

Definition qd2200 := (if_then_else_M ((EQ_M (reveal (f mphi44)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1)) &(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   mx42rn1 (if_then_else_M ((EQ_M (reveal (f mphi44)) (i 2) ) & (EQ_M (to (f mphi43)) (i 2)) &(EQ_M (to (f mphi42)) (i 2)) & (notb (EQ_M ( act(f mphi43)) new)) &(EQ_M (act (f mphi42)) new))   mf4ph41rn3 O)).

Definition qd2100_s := (if_then_else_M (EQ_M (reveal (f mphi43)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1)) &(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   O (if_then_else_M (EQ_M (to (f mphi43)) (i 2)) qd2200 O ) )).

Definition qd1200_s := (if_then_else_M (EQ_M (reveal (f mphi43)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi41)) (i 2)) &(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))  O (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi42)) (i 2)) &(EQ_M (to (f mphi41)) (i 2)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi41)) new))  O (if_then_else_M (EQ_M (to (f mphi43)) (i 1)) qd2200 O)) ) ).
Definition qd2001_s :=  (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1)) &(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   O (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 1) ) & (EQ_M (to (f mphi42)) (i 1)) &(EQ_M (to (f mphi41)) (i 1)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi41)) new))   O O )).
(*****************************Changes in protocol2********************************)
Definition qd0210_s :=  (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi42)) (i 1)) &(EQ_M (to (f mphi41)) (i 2))&(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi40)) new) &(EQ_M (m (f mphi41)) grn41) &(EQ_M (m (f mphi42)) grn43))   O (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 1) ) & (EQ_M (to (f mphi42)) (i 1)) &(EQ_M (to (f mphi41)) (i 2))&(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi40)) new) &(EQ_M (m (f mphi41)) grn41) &(EQ_M (m (f mphi42)) grn43))   O (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi41)) (i 2)) &(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))  O O ))).
Definition qd0120_s := (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 1) ) & (EQ_M (to (f mphi42)) (i 2)) &(EQ_M (to (f mphi41)) (i 1))&(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi40)) new) &(EQ_M (m (f mphi41)) grn41) &(EQ_M (m (f mphi42)) grn43))   O (if_then_else_M ((EQ_M (reveal (f mphi43)) (i 2) ) & (EQ_M (to (f mphi42)) (i 2)) &(EQ_M (to (f mphi41)) (i 1))&(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi42)) new)) &(EQ_M (act (f mphi40)) new) &(EQ_M (m (f mphi41)) grn41) &(EQ_M (m (f mphi42)) grn43))   O (if_then_else_M (EQ_M (reveal (f mphi43)) (i 1) ) O ( if_then_else_M (EQ_M (to (f mphi41)) (i 2)) O O)))).
(********************************************************************************)
Definition qd2000_ss :=  (if_then_else_M (EQ_M (reveal (f mphi42)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1)) &(EQ_M (to (f mphi40)) (i 1)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new)) O (if_then_else_M ((EQ_M (to (f mphi42)) (i 2)) & (EQ_M (act (f mphi42)) new)) qd2100 (if_then_else_M (EQ_M (to (f mphi42)) (i 2)) qd2001 O) ) ) ).


Definition qd1100_ss := (if_then_else_M (EQ_M (reveal (f mphi42)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi42)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi42)) (i 1)) qd2100_s (if_then_else_M ((EQ_M (to (f mphi42)) (i 2)) ) qd1200_s O) ))).
Definition qd1001_ss := (if_then_else_M (EQ_M (reveal (f mphi42)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 2) ) & (EQ_M (to (f mphi40)) (i 2)))  O (if_then_else_M (EQ_M (to (f mphi42)) (i 1)) qd2001_s O))).

Definition qd0110_ss := (if_then_else_M (EQ_M (reveal (f mphi42)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1)))  qd0120 (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 1) ) & (EQ_M (to (f mphi41)) (i 1))) qd0120_s  (if_then_else_M (EQ_M (to (f mphi42)) (i 2)) qd0210_s O)))).

Definition qd0200_ss :=  (if_then_else_M (EQ_M (reveal (f mphi42)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi42)) (i 2) ) & (EQ_M (to (f mphi41)) (i 2)) &(EQ_M (to (f mphi40)) (i 2)) & (notb (EQ_M ( act(f mphi41)) new)) &(EQ_M (act (f mphi40)) new))   O (if_then_else_M ((EQ_M (to (f mphi42)) (i 1)) & (EQ_M (act (f mphi42)) new)) qd1200_s (if_then_else_M (EQ_M (to (f mphi42)) (i 1)) qd0210_s O) ) ) ).
(**********************************************************************************************)

Definition qd1000_sss := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) qd2000_ss (if_then_else_M ((EQ_M (to (f mphi41)) (i 2)) & (EQ_M (act (f mphi41)) new)) qd1100_ss (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) qd1001_ss O))))).

Definition qd0010_sss := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi41)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi41)) (i 2)) & (EQ_M (act (f mphi41)) new)) qd0110_ss (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) O O) ) ) ).

Definition qd0100_sss := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi41)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi41)) (i 2)) qd0200_ss (if_then_else_M ((EQ_M (to (f mphi41)) (i 1)) & (EQ_M (act (f mphi41)) new)) qd1100_ss (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) qd0110_ss O))))).

Definition qd0001_sss := (if_then_else_M (EQ_M (reveal (f mphi41)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi41)) (i 1) ) & (EQ_M (to (f mphi40)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi41)) (i 1)) & (EQ_M (act (f mphi41)) new)) qd1001_ss (if_then_else_M (EQ_M (to (f mphi41)) (i 1)) O O) ) ) ).

Definition t46 := msg (if_then_else_M (EQ_M (reveal (f mphi40)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi40)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi40)) (i 1)) & (EQ_M (act (f mphi40)) new)) qd1000_sss (if_then_else_M (EQ_M (to (f mphi40)) (i 1)) qd0010_sss (if_then_else_M ((EQ_M (to (f mphi40)) (i 2)) & (EQ_M (act (f mphi40)) new)) qd0100_sss (if_then_else_M (EQ_M (to (f mphi40)) (i 2)) qd0001_sss O) ) )))).

Definition phi45  := phi44 ++ [ t46].

(*************************************************************************************************)
(*************************************************************************************************)

