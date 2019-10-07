
Load "Pi2".
(******************************Protocol Pi2'' :**************************************************************************)



Definition t30 := msg (G (N 0)).
Definition t31 := msg (g (N 0)).
Definition phi30 := [t30; t31].
Definition mphi30 := (conv_mylist_listm phi30).
Definition msgt30 := (ostomsg t30).
Definition msgt31 := (ostomsg t31).
Definition grn31 := (exp msgt30 msgt31 (r (N 1))).
Definition qc0000:= (if_then_else_M (EQ_M (reveal (f mphi30)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi30)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi30)) (i 1)) & (EQ_M (act (f mphi30)) new)) grn31 (if_then_else_M (EQ_M (to (f mphi30)) (i 1)) grn31 (if_then_else_M ((EQ_M (to (f mphi30)) (i 2)) & (EQ_M (act (f mphi30)) new)) grn31 (if_then_else_M (EQ_M (to (f mphi30)) (i 2)) grn31 O) ) )))).
Definition t32:= msg qc0000.

Definition phi31 := phi30 ++ [ t32 ].

 (***********************************************************)
Definition msgt32:= (ostomsg t32).
Definition mphi31 := (conv_mylist_listm phi31).
Definition mx31rn1 := (exp msgt30 (m (f mphi30 )) (r (N 1))).
Definition mx31rn2 := (exp msgt30 (m (f mphi30 )) (r (N 2))).
Definition grn32:= (exp msgt30 msgt31 (r (N 2))).

(**********qc0000 -> qc1000, qc0010, qc0100, qc0001*************************************************)

Definition qc1000 := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) acc (if_then_else_M ((EQ_M (to (f mphi31)) (i 2)) & (EQ_M (act (f mphi31)) new)) grn32 (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) grn32 O))))).

Definition qc0010:= (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi31)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1))) mx31rn1 (if_then_else_M ((EQ_M (to (f mphi31)) (i 2)) & (EQ_M (act (f mphi31)) new)) grn32 (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) grn32 O) ) ) ).

Definition qc0100 := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) acc (if_then_else_M ((EQ_M (to (f mphi31)) (i 1)) & (EQ_M (act (f mphi31)) new)) grn31 (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) grn31 O))))).

Definition qc0001 :=(if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi31)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1))) mx31rn1 (if_then_else_M ((EQ_M (to (f mphi31)) (i 1)) & (EQ_M (act (f mphi31)) new)) grn32 (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) grn32 O) ) ) ).

Definition t33 := msg (if_then_else_M (EQ_M (reveal (f mphi30)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi30)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi30)) (i 1)) & (EQ_M (act (f mphi30)) new)) qc1000 (if_then_else_M (EQ_M (to (f mphi30)) (i 1)) qc0010 (if_then_else_M ((EQ_M (to (f mphi30)) (i 2)) & (EQ_M (act (f mphi30)) new)) qc0100 (if_then_else_M (EQ_M (to (f mphi30)) (i 2)) qc0001 O) ) )))).
Definition phi32:= phi31 ++ [t33].


(***************************************************************************)
Definition msgt33:= (ostomsg t33).
Definition mphi32 := (conv_mylist_listm phi32).

Definition mx32rn1 := (exp msgt30 (m (f mphi31 )) (r (N 1))).
Definition mx32rn2 := (exp msgt30 (m (f mphi31 )) (r (N 2))).
Definition grn33:= (exp msgt30 msgt31 (r (N 3))).



(************* qc1000 -> qc2000, qc1100, qc1001*******************************************************)

Definition qc2000 :=  (if_then_else_M (EQ_M (reveal (f mphi32)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1)) &(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   mx32rn1 (if_then_else_M ((EQ_M (to (f mphi32)) (i 2)) & (EQ_M (act (f mphi32)) new)) grn33 (if_then_else_M (EQ_M (to (f mphi32)) (i 2)) grn33 O) ) ) ).


Definition qc1100 := (if_then_else_M (EQ_M (reveal (f mphi32)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi32)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi32)) (i 1)) acc (if_then_else_M ((EQ_M (to (f mphi32)) (i 2)) ) acc O) ))).
Definition qc1001 := (if_then_else_M (EQ_M (reveal (f mphi32)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 2) ) & (EQ_M (to (f mphi30)) (i 2)))  mx31rn1 (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 2) ) & (EQ_M (to (f mphi31)) (i 2))) mx32rn2  (if_then_else_M (EQ_M (to (f mphi32)) (i 1)) acc O)))).
(************qc0010 -> qc0020, qc0110, qc0011*********************************************************)

Definition qc0110 := (if_then_else_M (EQ_M (reveal (f mphi32)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1)))  mx31rn1 (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1))) mx32rn2  (if_then_else_M (EQ_M (to (f mphi32)) (i 2)) acc O)))).

(*****************qc0100 -> qc0200, qc1100, qc0110****************************************************)

Definition qc0200 :=  (if_then_else_M (EQ_M (reveal (f mphi32)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 2) ) & (EQ_M (to (f mphi31)) (i 2)) &(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   mx32rn1 (if_then_else_M ((EQ_M (to (f mphi32)) (i 1)) & (EQ_M (act (f mphi32)) new)) grn33 (if_then_else_M (EQ_M (to (f mphi32)) (i 1)) grn33 O) ) ) ).

(******************qc0001 -> qc0002, qc1001, qc0011****************************************************)

(*****************************************************************************************************)

Definition qc1000_s := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) qc2000 (if_then_else_M ((EQ_M (to (f mphi31)) (i 2)) & (EQ_M (act (f mphi31)) new)) qc1100 (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) qc1001 O))))).

Definition qc0010_s := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi31)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi31)) (i 2)) & (EQ_M (act (f mphi31)) new)) qc0110 (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) O O) ) ) ).

Definition qc0100_s := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) qc0200 (if_then_else_M ((EQ_M (to (f mphi31)) (i 1)) & (EQ_M (act (f mphi31)) new)) qc1100 (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) qc0110 O))))).

Definition qc0001_s := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi31)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi31)) (i 1)) & (EQ_M (act (f mphi31)) new)) qc1001 (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) O O) ) ) ).

Definition t34 := msg (if_then_else_M (EQ_M (reveal (f mphi30)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi30)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi30)) (i 1)) & (EQ_M (act (f mphi30)) new)) qc1000_s (if_then_else_M (EQ_M (to (f mphi30)) (i 1)) qc0010_s (if_then_else_M ((EQ_M (to (f mphi30)) (i 2)) & (EQ_M (act (f mphi30)) new)) qc0100_s (if_then_else_M (EQ_M (to (f mphi30)) (i 2)) qc0001_s O) ) )))).

Definition phi33:= phi32 ++ [t34].
(***********************************************************************************************)
Definition mx33rn2 := (exp msgt30 (m (f mphi32 )) (r (N 2))).
Definition mx33rn1 := (exp msgt30 (m (f mphi32 )) (r (N 1))).
Definition mphi33 := (conv_mylist_listm phi33).

(********************qc2000 -> qc3000, qc2100, qc2001****************************************************)
Definition qc2100 := (if_then_else_M (EQ_M (reveal (f mphi33)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1)) &(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   mx32rn1 (if_then_else_M (EQ_M (to (f mphi33)) (i 2)) acc O ) )).
(**************************qc1100 -> qc2100, qc1200 *****************************************************)
Definition qc1200 := (if_then_else_M (EQ_M (reveal (f mphi33)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi31)) (i 2)) &(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   mx32rn1 (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi32)) (i 2)) &(EQ_M (to (f mphi31)) (i 2)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi31)) new))   mx33rn2 (if_then_else_M (EQ_M (to (f mphi33)) (i 1)) acc O)) ) ).
(**********Changes to the states qc2001, qc0210 in protocol2**************************************************)
(**Definition grn34:= (exp msgt30 msgt31 (r (N 4))).**)
Definition qc2001 := (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi32)) (i 1)) &(EQ_M (to (f mphi31)) (i 2))&(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi30)) new) &(EQ_M (m (f mphi31)) grn31) &(EQ_M (m (f mphi32)) grn12))   mx32rn2 (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 1) ) & (EQ_M (to (f mphi32)) (i 1)) &(EQ_M (to (f mphi31)) (i 2))&(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi30)) new) &(EQ_M (m (f mphi31)) grn31) &(EQ_M (m (f mphi32)) grn12))   mx33rn1 (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 1) ) & (EQ_M (to (f mphi32)) (i 1)) &(EQ_M (to (f mphi31)) (i 1)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi31)) new))   mx33rn2 O ))).
 
Definition qc0210 :=  (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 1) ) & (EQ_M (to (f mphi32)) (i 2)) &(EQ_M (to (f mphi31)) (i 1))&(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi30)) new) &(EQ_M (m (f mphi31)) grn31) &(EQ_M (m (f mphi32)) grn12))   mx32rn2 (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi32)) (i 2)) &(EQ_M (to (f mphi31)) (i 1))&(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi30)) new) &(EQ_M (m (f mphi31)) grn31) &(EQ_M (m (f mphi32)) grn12))  mx33rn1 (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi31)) (i 2)) &(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   mx32rn1 O ))).

(********************************************************************************************************)
Definition qc0120 := (if_then_else_M (EQ_M (reveal (f mphi33)) (i 1) ) O ( if_then_else_M (EQ_M (to (f mphi31)) (i 2)) grn33 O)).


(*****************************qc1001 -> qc1002, qc2001***************************************************)

Definition qc2000_s :=  (if_then_else_M (EQ_M (reveal (f mphi32)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1)) &(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new)) O (if_then_else_M ((EQ_M (to (f mphi32)) (i 2)) & (EQ_M (act (f mphi32)) new)) qc2100 (if_then_else_M (EQ_M (to (f mphi32)) (i 2)) qc2001 O) ) ) ).


Definition qc1100_s := (if_then_else_M (EQ_M (reveal (f mphi32)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi32)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi32)) (i 1)) qc2100 (if_then_else_M ((EQ_M (to (f mphi32)) (i 2)) ) qc1200 O) ))).
Definition qc1001_s := (if_then_else_M (EQ_M (reveal (f mphi32)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 2) ) & (EQ_M (to (f mphi30)) (i 2)))  O (if_then_else_M (EQ_M (to (f mphi32)) (i 1)) qc2001 O))).

Definition qc0110_s := (if_then_else_M (EQ_M (reveal (f mphi32)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1)))  qc0120 (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1))) qc0120  (if_then_else_M (EQ_M (to (f mphi32)) (i 2)) qc0210 O)))).

Definition qc0200_s :=  (if_then_else_M (EQ_M (reveal (f mphi32)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 2) ) & (EQ_M (to (f mphi31)) (i 2)) &(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   O (if_then_else_M ((EQ_M (to (f mphi32)) (i 1)) & (EQ_M (act (f mphi32)) new)) qc1200 (if_then_else_M (EQ_M (to (f mphi32)) (i 1)) qc0210 O) ) ) ).
(***********************************************************************************************************)


Definition qc1000_ss := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) qc2000_s (if_then_else_M ((EQ_M (to (f mphi31)) (i 2)) & (EQ_M (act (f mphi31)) new)) qc1100_s (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) qc1001_s O))))).

Definition qc0010_ss := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi31)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi31)) (i 2)) & (EQ_M (act (f mphi31)) new)) qc0110_s (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) O O) ) ) ).

Definition qc0100_ss := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) qc0200_s (if_then_else_M ((EQ_M (to (f mphi31)) (i 1)) & (EQ_M (act (f mphi31)) new)) qc1100_s (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) qc0110_s O))))).

Definition qc0001_ss := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi31)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi31)) (i 1)) & (EQ_M (act (f mphi31)) new)) qc1001_s (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) O O) ) ) ).

Definition t35 := msg (if_then_else_M (EQ_M (reveal (f mphi30)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi30)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi30)) (i 1)) & (EQ_M (act (f mphi30)) new)) qc1000_ss (if_then_else_M (EQ_M (to (f mphi30)) (i 1)) qc0010_ss (if_then_else_M ((EQ_M (to (f mphi30)) (i 2)) & (EQ_M (act (f mphi30)) new)) qc0100_ss (if_then_else_M (EQ_M (to (f mphi30)) (i 2)) qc0001_ss O) ) )))).

Definition phi34 :=  phi33 ++ [ t35 ]. 

(***********************************************************************************************************)
Definition mx34rn3 := (exp msgt30 (m (f mphi33 )) (r (N 3))).
Definition mphi34 := (conv_mylist_listm phi34).

(********************qc2100 -> qc2200, qc3100************************************)

Definition qc2200 := (if_then_else_M ((EQ_M (reveal (f mphi34)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1)) &(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   mx32rn1 (if_then_else_M ((EQ_M (reveal (f mphi34)) (i 2) ) & (EQ_M (to (f mphi33)) (i 2)) &(EQ_M (to (f mphi32)) (i 2)) & (notb (EQ_M ( act(f mphi33)) new)) &(EQ_M (act (f mphi32)) new))   mx34rn3 O)).

Definition qc2100_s := (if_then_else_M (EQ_M (reveal (f mphi33)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1)) &(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   O (if_then_else_M (EQ_M (to (f mphi33)) (i 2)) qc2200 O ) )).

Definition qc1200_s := (if_then_else_M (EQ_M (reveal (f mphi33)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi31)) (i 2)) &(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))  O (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi32)) (i 2)) &(EQ_M (to (f mphi31)) (i 2)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi31)) new))  O (if_then_else_M (EQ_M (to (f mphi33)) (i 1)) qc2200 O)) ) ).
Definition qc2001_s :=  (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1)) &(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   O (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 1) ) & (EQ_M (to (f mphi32)) (i 1)) &(EQ_M (to (f mphi31)) (i 1)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi31)) new))   O O )).
(*****************************Changes in protocol2********************************)
Definition qc0210_s :=  (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi32)) (i 1)) &(EQ_M (to (f mphi31)) (i 2))&(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi30)) new) &(EQ_M (m (f mphi31)) grn31) &(EQ_M (m (f mphi32)) grn33))   O (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 1) ) & (EQ_M (to (f mphi32)) (i 1)) &(EQ_M (to (f mphi31)) (i 2))&(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi30)) new) &(EQ_M (m (f mphi31)) grn31) &(EQ_M (m (f mphi32)) grn33))   O (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi31)) (i 2)) &(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))  O O ))).
Definition qc0120_s := (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 1) ) & (EQ_M (to (f mphi32)) (i 2)) &(EQ_M (to (f mphi31)) (i 1))&(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi30)) new) &(EQ_M (m (f mphi31)) grn31) &(EQ_M (m (f mphi32)) grn33))   O (if_then_else_M ((EQ_M (reveal (f mphi33)) (i 2) ) & (EQ_M (to (f mphi32)) (i 2)) &(EQ_M (to (f mphi31)) (i 1))&(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi32)) new)) &(EQ_M (act (f mphi30)) new) &(EQ_M (m (f mphi31)) grn31) &(EQ_M (m (f mphi32)) grn33))   O (if_then_else_M (EQ_M (reveal (f mphi33)) (i 1) ) O ( if_then_else_M (EQ_M (to (f mphi31)) (i 2)) O O)))).
(********************************************************************************)
Definition qc2000_ss :=  (if_then_else_M (EQ_M (reveal (f mphi32)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1)) &(EQ_M (to (f mphi30)) (i 1)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new)) O (if_then_else_M ((EQ_M (to (f mphi32)) (i 2)) & (EQ_M (act (f mphi32)) new)) qc2100 (if_then_else_M (EQ_M (to (f mphi32)) (i 2)) qc2001 O) ) ) ).


Definition qc1100_ss := (if_then_else_M (EQ_M (reveal (f mphi32)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi32)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi32)) (i 1)) qc2100_s (if_then_else_M ((EQ_M (to (f mphi32)) (i 2)) ) qc1200_s O) ))).
Definition qc1001_ss := (if_then_else_M (EQ_M (reveal (f mphi32)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 2) ) & (EQ_M (to (f mphi30)) (i 2)))  O (if_then_else_M (EQ_M (to (f mphi32)) (i 1)) qc2001_s O))).

Definition qc0110_ss := (if_then_else_M (EQ_M (reveal (f mphi32)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1)))  qc0120 (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 1) ) & (EQ_M (to (f mphi31)) (i 1))) qc0120_s  (if_then_else_M (EQ_M (to (f mphi32)) (i 2)) qc0210_s O)))).

Definition qc0200_ss :=  (if_then_else_M (EQ_M (reveal (f mphi32)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi32)) (i 2) ) & (EQ_M (to (f mphi31)) (i 2)) &(EQ_M (to (f mphi30)) (i 2)) & (notb (EQ_M ( act(f mphi31)) new)) &(EQ_M (act (f mphi30)) new))   O (if_then_else_M ((EQ_M (to (f mphi32)) (i 1)) & (EQ_M (act (f mphi32)) new)) qc1200_s (if_then_else_M (EQ_M (to (f mphi32)) (i 1)) qc0210_s O) ) ) ).
(**********************************************************************************************)

Definition qc1000_sss := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) qc2000_ss (if_then_else_M ((EQ_M (to (f mphi31)) (i 2)) & (EQ_M (act (f mphi31)) new)) qc1100_ss (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) qc1001_ss O))))).

Definition qc0010_sss := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M ((EQ_M (reveal (f mphi31)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi31)) (i 2)) & (EQ_M (act (f mphi31)) new)) qc0110_ss (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) O O) ) ) ).

Definition qc0100_sss := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi31)) (i 2) ) O (if_then_else_M (EQ_M (to (f mphi31)) (i 2)) qc0200_ss (if_then_else_M ((EQ_M (to (f mphi31)) (i 1)) & (EQ_M (act (f mphi31)) new)) qc1100_ss (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) qc0110_ss O))))).

Definition qc0001_sss := (if_then_else_M (EQ_M (reveal (f mphi31)) (i 1) ) O (if_then_else_M ((EQ_M (reveal (f mphi31)) (i 1) ) & (EQ_M (to (f mphi30)) (i 1))) O (if_then_else_M ((EQ_M (to (f mphi31)) (i 1)) & (EQ_M (act (f mphi31)) new)) qc1001_ss (if_then_else_M (EQ_M (to (f mphi31)) (i 1)) O O) ) ) ).

Definition t36 := msg (if_then_else_M (EQ_M (reveal (f mphi30)) (i 1) ) O (if_then_else_M (EQ_M (reveal (f mphi30)) (i 2) ) O (if_then_else_M ((EQ_M (to (f mphi30)) (i 1)) & (EQ_M (act (f mphi30)) new)) qc1000_sss (if_then_else_M (EQ_M (to (f mphi30)) (i 1)) qc0010_sss (if_then_else_M ((EQ_M (to (f mphi30)) (i 2)) & (EQ_M (act (f mphi30)) new)) qc0100_sss (if_then_else_M (EQ_M (to (f mphi30)) (i 2)) qc0001_sss O) ) )))).

Definition phi35  := phi34 ++ [ t36].

(**************************************************************************************************)
(***************************************************************************************************)

Theorem RRS1: phi11 ~ phi31.
Proof. reflexivity. Qed.

Theorem RRS2: phi12 ~ phi32.
Proof. reflexivity. Qed.

Theorem RRS3: phi13 ~ phi33.
Proof. reflexivity. Qed.
Theorem RRS4: t15 ### t35.
Proof.  repeat try unfold phi35, phi15, phi34, phi14, phi33, phi13, phi32, phi12 ,phi31, phi11, phi30, phi10.
repeat try unfold t30, t10, t31,t32, t11,t12, t33, t13, t34, t14, t35, t15, t36, t16.
 
repeat try unfold qa0000, qa1000 , qa0010,qa0100,qa0001 ,qa2000,qa1100 ,qa1001 ,qa0110,qa0200,qa1000_s,qa0010_s,qa0100_s,qa0001_s,qa2100,qa1200,qa2001,qa0210,
 qa0120,qa2000_s, qa1100_s, qa1001_s, qa0110_s,qa0200_s,qa1000_ss,qa0010_ss, qa0100_ss,qa0001_ss,qa2200,qa2100_s,qa1200_s,qa2001_s,qa0210_s,qa0120_s,qa2000_ss,qa1100_ss ,qa1001_ss,qa0110_ss,qa0200_ss,
 qa1000_sss,qa0010_sss,qa0100_sss,qa0001_sss.
simpl.
repeat try unfold qc0000, qc1000 , qc0010,qc0100,qc0001 ,qc2000,qc1100 ,qc1001 ,qc0110,qc0200,qc1000_s,qc0010_s,qc0100_s,qc0001_s,qc2100,qc1200,qc2001,qc0210,
qc0120,qc2000_s, qc1100_s, qc1001_s, qc0110_s,qc0200_s.

try unfold qc1000_ss,qc0010_ss, qc0100_ss,qc0001_ss,qc2200,qc2100_s,qc1200_s,qc2001_s,qc0210_s,qc0120_s,qc2000_ss,qc1100_ss ,qc1001_ss,qc0110_ss,qc0200_ss,
qc1000_sss,qc0010_sss,qc0100_sss,qc0001_sss.
rewrite IFSAME_M with (b:= (EQ_M (to (f mphi11)) (i 1))) (x:= O) .
rewrite IFSAME_M with (b:= (EQ_M (to (f mphi31)) (i 1))) (x:= O) .
repeat try unfold qa0000, qa1000 , qa0010,qa0100,qa0001 ,qa2000,qa1100 ,qa1001 ,qa0110,qa0200,qa1000_s,qa0010_s,qa0100_s,qa0001_s,qa2100,qa1200,qa2001,qa0210,
 qa0120,qa2000_s, qa1100_s, qa1001_s, qa0110_s,qa0200_s,qa1000_ss,qa0010_ss, qa0100_ss,qa0001_ss,qa2200,qa2100_s,qa1200_s,qa2001_s,qa0210_s,qa0120_s,qa2000_ss,qa1100_ss ,qa1001_ss,qa0110_ss,qa0200_ss,
 qa1000_sss,qa0010_sss,qa0100_sss,qa0001_sss.
simpl.
repeat try unfold qc0000, qc1000 , qc0010,qc0100,qc0001 ,qc2000,qc1100 ,qc1001 ,qc0110,qc0200,qc1000_s,qc0010_s,qc0100_s,qc0001_s,qc2100,qc1200,qc2001,qc0210,
qc0120,qc2000_s, qc1100_s, qc1001_s, qc0110_s,qc0200_s.

try unfold qc1000_ss,qc0010_ss, qc0100_ss,qc0001_ss,qc2200,qc2100_s,qc1200_s,qc2001_s,qc0210_s,qc0120_s,qc2000_ss,qc1100_ss ,qc1001_ss,qc0110_ss,qc0200_ss,
qc1000_sss,qc0010_sss,qc0100_sss,qc0001_sss.

Admitted.


Theorem RRS5: phi14 ~ phi34.
Proof.  repeat try unfold phi35, phi15, phi34, phi14, phi33, phi13, phi32, phi12 ,phi31, phi11, phi30, phi10.
repeat try unfold t30, t10, t31,t32, t11,t12, t33, t13, t34, t14, t35, t15, t36, t16.
 
repeat try unfold qa0000, qa1000 , qa0010,qa0100,qa0001 ,qa2000,qa1100 ,qa1001 ,qa0110,qa0200,qa1000_s,qa0010_s,qa0100_s,qa0001_s,qa2100,qa1200,qa2001,qa0210,
 qa0120,qa2000_s, qa1100_s, qa1001_s, qa0110_s,qa0200_s,qa1000_ss,qa0010_ss, qa0100_ss,qa0001_ss,qa2200,qa2100_s,qa1200_s,qa2001_s,qa0210_s,qa0120_s,qa2000_ss,qa1100_ss ,qa1001_ss,qa0110_ss,qa0200_ss,
 qa1000_sss,qa0010_sss,qa0100_sss,qa0001_sss.
simpl.
repeat try unfold qc0000, qc1000 , qc0010,qc0100,qc0001 ,qc2000,qc1100 ,qc1001 ,qc0110,qc0200,qc1000_s,qc0010_s,qc0100_s,qc0001_s,qc2100,qc1200,qc2001,qc0210,
qc0120,qc2000_s, qc1100_s, qc1001_s, qc0110_s,qc0200_s.

try unfold qc1000_ss,qc0010_ss, qc0100_ss,qc0001_ss,qc2200,qc2100_s,qc1200_s,qc2001_s,qc0210_s,qc0120_s,qc2000_ss,qc1100_ss ,qc1001_ss,qc0110_ss,qc0200_ss,
qc1000_sss,qc0010_sss,qc0100_sss,qc0001_sss.

pose proof(IFSAME_M).
rewrite IFSAME_M with (b:= (EQ_M (to (f mphi11)) (i 1))) (x:= O) .
rewrite IFSAME_M with (b:= (EQ_M (to (f mphi31)) (i 1))) (x:= O) .
repeat try unfold qc0000, qc1000 , qc0010,qc0100,qc0001 ,qc2000,qc1100 ,qc1001 ,qc0110,qc0200,qc1000_s,qc0010_s,qc0100_s,qc0001_s,qc2100,qc1200,qc2001,qc0210,
qc0120,qc2000_s, qc1100_s, qc1001_s, qc0110_s,qc0200_s.

try unfold qc1000_ss,qc0010_ss, qc0100_ss,qc0001_ss,qc2200,qc2100_s,qc1200_s,qc2001_s,qc0210_s,qc0120_s,qc2000_ss,qc1100_ss ,qc1001_ss,qc0110_ss,qc0200_ss,
qc1000_sss,qc0010_sss,qc0100_sss,qc0001_sss.

try unfold mphi25 , mphi24 , mphi23 , mphi22. try unfold mphi21, mphi20.
 try unfold mphi35 , mphi34 , mphi33 , mphi32. try unfold mphi31, mphi30. simpl.

 repeat try unfold phi35, phi15, phi34, phi14, phi33, phi13, phi32, phi12 ,phi31, phi11, phi30, phi10 .
repeat try unfold t30, t10, t31,t32, t11,t12, t33, t13, t34, t14, t35, t15, t36, t16.
 try unfold mphi15 , mphi14 , mphi13 , mphi12. try unfold mphi11, mphi10.
 try unfold mphi35 , mphi34 , mphi33 , mphi32. try unfold mphi31, mphi30. simpl.

repeat try unfold qa0000, qa1000 , qa0010,qa0100,qa0001 ,qa2000,qa1100 ,qa1001 ,qa0110,qa0200,qa1000_s,qa0010_s,qa0100_s,qa0001_s,qa2100,qa1200,qa2001,qa0210,
 qa0120,qa2000_s, qa1100_s, qa1001_s, qa0110_s,qa0200_s,qa1000_ss,qa0010_ss, qa0100_ss,qa0001_ss,qa2200,qa2100_s,qa1200_s,qa2001_s,qa0210_s,qa0120_s,qa2000_ss,qa1100_ss ,qa1001_ss,qa0110_ss,qa0200_ss,
 qa1000_sss,qa0010_sss,qa0100_sss,qa0001_sss.

repeat try unfold qc0000, qc1000 , qc0010,qc0100,qc0001 ,qc2000,qc1100 ,qc1001 ,qc0110,qc0200,qc1000_s,qc0010_s,qc0100_s,qc0001_s,qc2100,qc1200,qc2001,qc0210,
 qc0120,qc2000_s, qc1100_s, qc1001_s, qc0110_s,qc0200_s,qc1000_ss,qc0010_ss, qc0100_ss,qc0001_ss,qc2200,qc2100_s,qc1200_s,qc2001_s,qc0210_s,qc0120_s,qc2000_ss,qc1100_ss ,qc1001_ss,qc0110_ss,qc0200_ss,
 qc1000_sss,qc0010_sss,qc0100_sss,qc0001_sss.

 repeat try unfold phi35, phi15, phi34, phi14, phi33, phi13, phi32, phi12 ,phi31, phi11, phi30, phi10 .
Admitted.

Theorem RRS7: [t14] ~ [t34]. 
Proof. repeat try unfold t30, t10, t31,t32, t11,t12, t33, t13, t34, t14, t35, t15, t36, t16.
repeat try unfold qa0000, qa1000 , qa0010,qa0100,qa0001 ,qa2000,qa1100 ,qa1001 ,qa0110,qa0200,qa1000_s,qa0010_s,qa0100_s,qa0001_s,qa2100,qa1200,qa2001,qa0210,
 qa0120,qa2000_s, qa1100_s, qa1001_s, qa0110_s,qa0200_s,qa1000_ss,qa0010_ss, qa0100_ss,qa0001_ss,qa2200,qa2100_s,qa1200_s,qa2001_s,qa0210_s,qa0120_s,qa2000_ss,qa1100_ss ,qa1001_ss,qa0110_ss,qa0200_ss,
 qa1000_sss,qa0010_sss,qa0100_sss,qa0001_sss.

repeat try unfold qc0000, qc1000 , qc0010,qc0100,qc0001 ,qc2000,qc1100 ,qc1001 ,qc0110,qc0200,qc1000_s,qc0010_s,qc0100_s,qc0001_s,qc2100,qc1200,qc2001,qc0210,
 qc0120,qc2000_s, qc1100_s, qc1001_s, qc0110_s,qc0200_s,qc1000_ss,qc0010_ss, qc0100_ss,qc0001_ss,qc2200,qc2100_s,qc1200_s,qc2001_s,qc0210_s,qc0120_s,qc2000_ss,qc1100_ss ,qc1001_ss,qc0110_ss,qc0200_ss,
 qc1000_sss,qc0010_sss,qc0100_sss,qc0001_sss.
try unfold mphi15 , mphi14 , mphi13.  try unfold mphi12, mphi11, mphi10.
 try unfold mphi35 , mphi34 , mphi33 , mphi32. try unfold mphi31, mphi30. simpl.
try unfold mphi15 , mphi14 , mphi13 , mphi12. try unfold mphi11, mphi10.
 try unfold mphi35 , mphi34 , mphi33 , mphi32. try unfold mphi31, mphi30. simpl.
Admitted.
