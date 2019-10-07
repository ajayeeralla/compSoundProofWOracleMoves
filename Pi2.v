Load "Pi1".
(***********************protocol Pi2 :  The oracle reveals randomly generated key if there are two sessions in which the same key computed otherwise the actual key***************************************************)


Definition t20 := msg (G (N 0)).
Definition t21 := msg (g (N 0)).
Definition phi20 := [t20; t21].
Definition mphi20 := (conv_mylist_listm phi20).
Definition msgt20 := (ostomsg t20).
Definition msgt21 := (ostomsg t21).

Definition grn21 := (exp msgt20 msgt21 (r (N 1))).
Definition qb0000:= (if_then_else_M (EQ_M (reveal (f mphi20)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi20)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi20)) (i 1)) & (EQ_M (act (f mphi20)) new)) grn21 (if_then_else_M (EQ_M (to (f mphi20)) (i 1)) grn21 (if_then_else_M ((EQ_M (to (f mphi20)) (i 2)) & (EQ_M (act (f mphi20)) new)) grn21 (if_then_else_M (EQ_M (to (f mphi20)) (i 2)) grn21 O) ) )))).
Definition t22:= msg qb0000.

Definition phi21 := phi20 ++ [ t22 ].

 (***********************************************************)
(************************************************************)
Definition msgt22:= (ostomsg t22).
Definition mphi21 := (conv_mylist_listm phi21).


Definition mx21rn1 := (exp msgt20 (m (f mphi20 )) (r (N 1))).
 Definition mx21rn2 := (exp msgt20 (m (f mphi20 )) (r (N 2))).

Definition grn22:= (exp msgt20 msgt21 (r (N 2))).

(**********qb0000 -> qb1000, qb0010, qb0100, qb0001*************************************************)

Definition qb1000 := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) acc (if_then_else_M ((EQ_M (to (f mphi21)) (i 2)) & (EQ_M (act (f mphi21)) new)) grn22 (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) grn22 O))))).

Definition qb0010:= (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi21)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1))) mx21rn1 (if_then_else_M ((EQ_M (to (f mphi21)) (i 2)) & (EQ_M (act (f mphi21)) new)) grn22 (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) grn22 O) ) ) ).

Definition qb0100 := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) acc (if_then_else_M ((EQ_M (to (f mphi21)) (i 1)) & (EQ_M (act (f mphi21)) new)) grn21 (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) grn21 O))))).

Definition qb0001 :=(if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi21)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1))) mx21rn1 (if_then_else_M ((EQ_M (to (f mphi21)) (i 1)) & (EQ_M (act (f mphi21)) new)) grn22 (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) grn22 O) ) ) ).

Definition t23 := msg (if_then_else_M (EQ_M (reveal (f mphi20)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi20)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi20)) (i 1)) & (EQ_M (act (f mphi20)) new)) qb1000 (if_then_else_M (EQ_M (to (f mphi20)) (i 1)) qb0010 (if_then_else_M ((EQ_M (to (f mphi20)) (i 2)) & (EQ_M (act (f mphi20)) new)) qb0100 (if_then_else_M (EQ_M (to (f mphi20)) (i 2)) qb0001 O) ) )))).
Definition phi22:= phi21 ++ [t23].


(***************************************************************************)
(***************************************************************************)
Definition msgt23:= (ostomsg t23).
Definition mphi22 := (conv_mylist_listm phi22).

Definition mx22rn1 := (exp msgt20 (m (f mphi21 )) (r (N 1))).
Definition mx22rn2 := (exp msgt20 (m (f mphi21 )) (r (N 2))).
Definition grn23:= (exp msgt20 msgt21 (r (N 3))).



(************* qb1000 -> qb2000, qb1100, qb1001*******************************************************)

Definition qb2000 :=  (if_then_else_M (EQ_M (reveal (f mphi22)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1)) &(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   mx22rn1 (if_then_else_M ((EQ_M (to (f mphi22)) (i 2)) & (EQ_M (act (f mphi22)) new)) grn23 (if_then_else_M (EQ_M (to (f mphi22)) (i 2)) grn23 O) ) ) ).


Definition qb1100 := (if_then_else_M (EQ_M (reveal (f mphi22)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi22)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi22)) (i 1)) acc (if_then_else_M ((EQ_M (to (f mphi22)) (i 2)) ) acc O) ))).
Definition qb1001 := (if_then_else_M (EQ_M (reveal (f mphi22)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 2) ) & (EQ_M (to (f mphi20)) (i 2)))  mx21rn1 (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 2) ) & (EQ_M (to (f mphi21)) (i 2))) mx22rn2  (if_then_else_M (EQ_M (to (f mphi22)) (i 1)) acc O)))).
(************qb0010 -> qb0020, qb0110, qb0011*********************************************************)

Definition qb0110 := (if_then_else_M (EQ_M (reveal (f mphi22)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1)))  mx21rn1 (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1))) mx22rn2  (if_then_else_M (EQ_M (to (f mphi22)) (i 2)) acc O)))).

(*****************qb0100 -> qb0200, qb1100, qb0110****************************************************)

Definition qb0200 :=  (if_then_else_M (EQ_M (reveal (f mphi22)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 2) ) & (EQ_M (to (f mphi21)) (i 2)) &(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   mx22rn1 (if_then_else_M ((EQ_M (to (f mphi22)) (i 1)) & (EQ_M (act (f mphi22)) new)) grn23 (if_then_else_M (EQ_M (to (f mphi22)) (i 1)) grn23 O) ) ) ).

(******************qb0001 -> qb0002, qb1001, qb0011****************************************************)

(*****************************************************************************************************)

Definition qb1000_s := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) qb2000 (if_then_else_M ((EQ_M (to (f mphi21)) (i 2)) & (EQ_M (act (f mphi21)) new)) qb1100 (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) qb1001 O))))).

Definition qb0010_s := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi21)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi21)) (i 2)) & (EQ_M (act (f mphi21)) new)) qb0110 (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) O O) ) ) ).

Definition qb0100_s := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) qb0200 (if_then_else_M ((EQ_M (to (f mphi21)) (i 1)) & (EQ_M (act (f mphi21)) new)) qb1100 (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) qb0110 O))))).

Definition qb0001_s := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi21)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi21)) (i 1)) & (EQ_M (act (f mphi21)) new)) qb1001 (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) O O) ) ) ).

Definition t24 := msg (if_then_else_M (EQ_M (reveal (f mphi20)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi20)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi20)) (i 1)) & (EQ_M (act (f mphi20)) new)) qb1000_s (if_then_else_M (EQ_M (to (f mphi20)) (i 1)) qb0010_s (if_then_else_M ((EQ_M (to (f mphi20)) (i 2)) & (EQ_M (act (f mphi20)) new)) qb0100_s (if_then_else_M (EQ_M (to (f mphi20)) (i 2)) qb0001_s O) ) )))).

Definition phi23:= phi22 ++ [t24].
(***********************************************************************************************)
(***********************************************************************************************)
Definition mx23rn2 := (exp msgt20 (m (f mphi22 )) (r (N 2))).
Definition mphi23 := (conv_mylist_listm phi23).

(********************qb2000 -> qb3000, qb2100, qb2001****************************************************)
Definition qb2100 := (if_then_else_M (EQ_M (reveal (f mphi23)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1)) &(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   mx22rn1 (if_then_else_M (EQ_M (to (f mphi23)) (i 2)) acc O ) )).
(**************************qb1100 -> qb2100, qb1200 *****************************************************)
Definition qb1200 := (if_then_else_M (EQ_M (reveal (f mphi23)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi21)) (i 2)) &(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   mx22rn1 (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi22)) (i 2)) &(EQ_M (to (f mphi21)) (i 2)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi21)) new))   mx23rn2 (if_then_else_M (EQ_M (to (f mphi23)) (i 1)) acc O)) ) ).
(**********Changes to the states qb2001, qb0210 in protocol2**************************************************)
Definition grn24:= (exp msgt20 msgt21 (r (N 4))).
Definition qb2001 := (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi22)) (i 1)) &(EQ_M (to (f mphi21)) (i 2))&(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi20)) new) &(EQ_M (m (f mphi21)) grn21) &(EQ_M (m (f mphi22)) grn22))   grn24 (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 1) ) & (EQ_M (to (f mphi22)) (i 1)) &(EQ_M (to (f mphi21)) (i 2))&(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi20)) new) &(EQ_M (m (f mphi21)) grn21) &(EQ_M (m (f mphi22)) grn22))   grn24  (if_then_else_M ((EQ_M (reveal (f mphi13)) (i 2) ) & (EQ_M (to (f mphi10)) (i 2))) mx11rn1  (if_then_else_M ((EQ_M (reveal (f mphi13)) (i 2) ) & (EQ_M (to (f mphi11)) (i 2))) mx12rn2 (if_then_else_M ((EQ_M (reveal (f mphi13)) (i 1) ) & (EQ_M (to (f mphi11)) (i 1)) &(EQ_M (to (f mphi10)) (i 1)) & (notb (EQ_M ( act(f mphi11)) new)) &(EQ_M (act (f mphi10)) new))   mx12rn1 (if_then_else_M ((EQ_M (reveal (f mphi13)) (i 1) ) & (EQ_M (to (f mphi12)) (i 1)) &(EQ_M (to (f mphi11)) (i 1)) & (notb (EQ_M ( act(f mphi12)) new)) &(EQ_M (act (f mphi11)) new))   mx13rn2 O)))))).
 
Definition qb0210 :=  (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 1) ) & (EQ_M (to (f mphi22)) (i 2)) &(EQ_M (to (f mphi21)) (i 1))&(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi20)) new) &(EQ_M (m (f mphi21)) grn11) &(EQ_M (m (f mphi22)) grn12))   grn24 (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi22)) (i 2)) &(EQ_M (to (f mphi21)) (i 1))&(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi20)) new) &(EQ_M (m (f mphi21)) grn21) &(EQ_M (m (f mphi22)) grn12))   grn24 (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi21)) (i 2)) &(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   mx22rn1 O ))).

(********************************************************************************************************)
Definition qb0120 := (if_then_else_M (EQ_M (reveal (f mphi23)) (i 1) ) O ( if_then_else_M (EQ_M (to (f mphi21)) (i 2)) grn23 O)).


(*****************************qb1001 -> qb1002, qb2001***************************************************)

Definition qb2000_s :=  (if_then_else_M (EQ_M (reveal (f mphi22)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1)) &(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new)) O (if_then_else_M ((EQ_M (to (f mphi22)) (i 2)) & (EQ_M (act (f mphi22)) new)) qb2100 (if_then_else_M (EQ_M (to (f mphi22)) (i 2)) qb2001 O) ) ) ).


Definition qb1100_s := (if_then_else_M (EQ_M (reveal (f mphi22)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi22)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi22)) (i 1)) qb2100 (if_then_else_M ((EQ_M (to (f mphi22)) (i 2)) ) qb1200 O) ))).
Definition qb1001_s := (if_then_else_M (EQ_M (reveal (f mphi22)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 2) ) & (EQ_M (to (f mphi20)) (i 2)))  O (if_then_else_M (EQ_M (to (f mphi22)) (i 1)) qb2001 O))).

Definition qb0110_s := (if_then_else_M (EQ_M (reveal (f mphi22)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1)))  qb0120 (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1))) qb0120  (if_then_else_M (EQ_M (to (f mphi22)) (i 2)) qb0210 O)))).

Definition qb0200_s :=  (if_then_else_M (EQ_M (reveal (f mphi22)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 2) ) & (EQ_M (to (f mphi21)) (i 2)) &(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   O (if_then_else_M ((EQ_M (to (f mphi22)) (i 1)) & (EQ_M (act (f mphi22)) new)) qb1200 (if_then_else_M (EQ_M (to (f mphi22)) (i 1)) qb0210 O) ) ) ).
(***********************************************************************************************************)


Definition qb1000_ss := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) qb2000_s (if_then_else_M ((EQ_M (to (f mphi21)) (i 2)) & (EQ_M (act (f mphi21)) new)) qb1100_s (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) qb1001_s O))))).

Definition qb0010_ss := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi21)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi21)) (i 2)) & (EQ_M (act (f mphi21)) new)) qb0110_s (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) O O) ) ) ).

Definition qb0100_ss := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) qb0200_s (if_then_else_M ((EQ_M (to (f mphi21)) (i 1)) & (EQ_M (act (f mphi21)) new)) qb1100_s (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) qb0110_s O))))).

Definition qb0001_ss := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi21)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi21)) (i 1)) & (EQ_M (act (f mphi21)) new)) qb1001_s (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) O O) ) ) ).

Definition t25 := msg (if_then_else_M (EQ_M (reveal (f mphi20)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi20)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi20)) (i 1)) & (EQ_M (act (f mphi20)) new)) qb1000_ss (if_then_else_M (EQ_M (to (f mphi20)) (i 1)) qb0010_ss (if_then_else_M ((EQ_M (to (f mphi20)) (i 2)) & (EQ_M (act (f mphi20)) new)) qb0100_ss (if_then_else_M (EQ_M (to (f mphi20)) (i 2)) qb0001_ss O) ) )))).

Definition phi24 :=  phi23 ++ [ t25 ]. 

(***********************************************************************************************************)
(***********************************************************************************************************)
Definition mx24rn3 := (exp msgt20 (m (f mphi23 )) (r (N 3))).
Definition mphi24 := (conv_mylist_listm phi24).

(********************qb2100 -> qb2200, qb3100************************************)

Definition qb2200 := (if_then_else_M ((EQ_M (reveal (f mphi24)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1)) &(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   mx22rn1 (if_then_else_M ((EQ_M (reveal (f mphi24)) (i 2) ) & (EQ_M (to (f mphi23)) (i 2)) &(EQ_M (to (f mphi22)) (i 2)) & (notb (EQ_M ( act(f mphi23)) new)) &(EQ_M (act (f mphi22)) new))   mx24rn3 O)).

Definition qb2100_s := (if_then_else_M (EQ_M (reveal (f mphi23)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1)) &(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   O (if_then_else_M (EQ_M (to (f mphi23)) (i 2)) qb2200 O ) )).

Definition qb1200_s := (if_then_else_M (EQ_M (reveal (f mphi23)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi21)) (i 2)) &(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))  O (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi22)) (i 2)) &(EQ_M (to (f mphi21)) (i 2)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi21)) new))  O (if_then_else_M (EQ_M (to (f mphi23)) (i 1)) qb2200 O)) ) ).
Definition qb2001_s :=  (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1)) &(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   O (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 1) ) & (EQ_M (to (f mphi22)) (i 1)) &(EQ_M (to (f mphi21)) (i 1)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi21)) new))   O O )).
(*****************************Changes in protocol2********************************)
Definition qb0210_s :=  (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi22)) (i 1)) &(EQ_M (to (f mphi21)) (i 2))&(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi20)) new) &(EQ_M (m (f mphi21)) grn21) &(EQ_M (m (f mphi22)) grn12))   O (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 1) ) & (EQ_M (to (f mphi22)) (i 1)) &(EQ_M (to (f mphi21)) (i 2))&(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi20)) new) &(EQ_M (m (f mphi21)) grn21) &(EQ_M (m (f mphi22)) grn12))   O (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi21)) (i 2)) &(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))  O O ))).
Definition qb0120_s := (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 1) ) & (EQ_M (to (f mphi22)) (i 2)) &(EQ_M (to (f mphi21)) (i 1))&(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi20)) new) &(EQ_M (m (f mphi21)) grn21) &(EQ_M (m (f mphi22)) grn12))   O (if_then_else_M ((EQ_M (reveal (f mphi23)) (i 2) ) & (EQ_M (to (f mphi22)) (i 2)) &(EQ_M (to (f mphi21)) (i 1))&(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi22)) new)) &(EQ_M (act (f mphi20)) new) &(EQ_M (m (f mphi21)) grn21) &(EQ_M (m (f mphi22)) grn12))   O (if_then_else_M (EQ_M (reveal (f mphi23)) (i 1) ) O ( if_then_else_M (EQ_M (to (f mphi21)) (i 2)) O O)))).
(********************************************************************************)
Definition qb2000_ss :=  (if_then_else_M (EQ_M (reveal (f mphi22)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1)) &(EQ_M (to (f mphi20)) (i 1)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new)) O (if_then_else_M ((EQ_M (to (f mphi22)) (i 2)) & (EQ_M (act (f mphi22)) new)) qb2100 (if_then_else_M (EQ_M (to (f mphi22)) (i 2)) qb2001 O) ) ) ).


Definition qb1100_ss := (if_then_else_M (EQ_M (reveal (f mphi22)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi22)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi22)) (i 1)) qb2100_s (if_then_else_M ((EQ_M (to (f mphi22)) (i 2)) ) qb1200_s O) ))).
Definition qb1001_ss := (if_then_else_M (EQ_M (reveal (f mphi22)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 2) ) & (EQ_M (to (f mphi20)) (i 2)))  O (if_then_else_M (EQ_M (to (f mphi22)) (i 1)) qb2001_s O))).

Definition qb0110_ss := (if_then_else_M (EQ_M (reveal (f mphi22)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1)))  qb0120 (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 1) ) & (EQ_M (to (f mphi21)) (i 1))) qb0120_s  (if_then_else_M (EQ_M (to (f mphi22)) (i 2)) qb0210_s O)))).

Definition qb0200_ss :=  (if_then_else_M (EQ_M (reveal (f mphi22)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi22)) (i 2) ) & (EQ_M (to (f mphi21)) (i 2)) &(EQ_M (to (f mphi20)) (i 2)) & (notb (EQ_M ( act(f mphi21)) new)) &(EQ_M (act (f mphi20)) new))   O (if_then_else_M ((EQ_M (to (f mphi22)) (i 1)) & (EQ_M (act (f mphi22)) new)) qb1200_s (if_then_else_M (EQ_M (to (f mphi22)) (i 1)) qb0210_s O) ) ) ).
(**********************************************************************************************)

Definition qb1000_sss := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) qb2000_ss (if_then_else_M ((EQ_M (to (f mphi21)) (i 2)) & (EQ_M (act (f mphi21)) new)) qb1100_ss (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) qb1001_ss O))))).

Definition qb0010_sss := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi21)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi21)) (i 2)) & (EQ_M (act (f mphi21)) new)) qb0110_ss (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) O O) ) ) ).

Definition qb0100_sss := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi21)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi21)) (i 2)) qb0200_ss (if_then_else_M ((EQ_M (to (f mphi21)) (i 1)) & (EQ_M (act (f mphi21)) new)) qb1100_ss (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) qb0110_ss O))))).

Definition qb0001_sss := (if_then_else_M (EQ_M (reveal (f mphi21)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi21)) (i 1) ) & (EQ_M (to (f mphi20)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi21)) (i 1)) & (EQ_M (act (f mphi21)) new)) qb1001_ss (if_then_else_M (EQ_M (to (f mphi21)) (i 1)) O O) ) ) ).

Definition t26 := msg (if_then_else_M (EQ_M (reveal (f mphi20)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi20)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi20)) (i 1)) & (EQ_M (act (f mphi20)) new)) qb1000_sss (if_then_else_M (EQ_M (to (f mphi20)) (i 1)) qb0010_sss (if_then_else_M ((EQ_M (to (f mphi20)) (i 2)) & (EQ_M (act (f mphi20)) new)) qb0100_sss (if_then_else_M (EQ_M (to (f mphi20)) (i 2)) qb0001_sss O) ) )))).

Definition phi25  := phi24 ++ [ t26].
(**********************************************************************************************)
(**********************************************************************************************)
