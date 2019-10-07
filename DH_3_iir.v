Load "tactics".

(*****************DH_3_iir***********************)
(*************DH protocol for three sessions, initiator, initiator, responder************)

(*****************Real or random Secrecy*****************************************)
(********************************************************************************)
(******protocol Pi1 :The oracle reveals the actual Key if there is any*************)

(********************************************************************************)


Definition phi0  := [ msg (G 0) ; msg (g 0)].
Definition mphi0 := (conv_mylist_listm phi0).
Definition grn (n:nat) := (exp (G 0) (g 0) (r n)).

Definition x1 := (f mphi0).
(******start state****************)
Definition qa000:= (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) (grn 1 ) (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) (grn 2 ) (if_then_else_M (EQ_M (to x1) (i 3)) (grn 3)   O) ) )))).

(************************)
Definition t12:= msg qa000.
Definition phi1 := phi0 ++ [ t12 ].


(***********************************************************)

Definition mphi1 := (conv_mylist_listm phi1).
Definition mx1rn1 := (exp (G 0) (m x1) (r 1)).
Definition mx1rn2 := (exp (G 0) (m x1) (r 2)).
Definition mx1rn3 := (exp (G 0) (m x1) (r 3)).
Definition grn2:= (exp (G 0) (g 0) (r 2)).

Definition x2 := (f mphi1).

Definition tta1 ( x2 x1 :message) (j :nat) := (EQ_M (reveal x2) (i j)) & (EQ_M (to x1) (i j)).
Definition tta2 (x3 x2 x1 :message) (j:nat) := (EQ_M (reveal x3) (i j)) & (EQ_M (to x2) (i j)) & (EQ_M (to x1) (i j))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new).

(**********qa0000 -> qa1000, qa0010, qa0100, qa0001*************************************************)

Definition qa100 :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) acc   (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) (grn 2) (if_then_else_M (EQ_M (to x2) (i 3)) (grn 3) O)))))).


Definition qa010 :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new) (grn 1) (if_then_else_M (EQ_M (to x2) (i 2)) acc (if_then_else_M (EQ_M (to x2) (i 3)) (grn 3) O)))))).

Definition qa001:= (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (to x2) (i 1)) (grn 1) (if_then_else_M (EQ_M (to x2) (i 2)) (grn 2) O))))).


Definition t13 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa100 (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qa010 (if_then_else_M (EQ_M (to x1) (i 3)) qa001   O) ) )))).

Definition phi2:= phi1 ++ [t13].



(***************************************************************************)

Definition mphi2 := (conv_mylist_listm phi2).
Definition mx2rn1 := (exp (G 0) (m x2) (r 1)).
Definition mx2rn2 := (exp (G 0) (m x2) (r 2)).

Definition mx2rn3 := (exp (G 0) (m x2) (r 3)).
Definition grn3:= (exp (G 0) (g 0) (r 3)).
Definition x3 := (f mphi2).



(************* qa100 -> qbar, qa200, qa110, qa101, qbar*******************************************************)

Definition qa200 := (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new) (grn 2) (if_then_else_M (EQ_M (to x3) (i 3)) (grn 3) O))))).

Definition qa110 := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1)) acc (if_then_else_M (EQ_M (to x3) (i 2)) acc (if_then_else_M (EQ_M (to x3) (i 3)) (grn 3) O)))))).


Definition qa101 :=  (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) acc
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) (grn 2) O)))))).


Definition qa020:= (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 1) (if_then_else_M (EQ_M (to x3) (i 1)) (grn 3)  O))))).

Definition qa011 := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 1) (if_then_else_M (EQ_M (to x3) (i 2)) acc  O)))))).


 

Definition qa002:=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 1) (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 2) O)))).

(***********************************************************************)


Definition qa100_s :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa200  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qa110 (if_then_else_M (EQ_M (to x2) (i 3)) qa101 O)))))).


Definition qa010_s :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qa020 (if_then_else_M (EQ_M (to x2) (i 3))  qa011 O)))))).

Definition qa001_s := (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa101 (if_then_else_M (EQ_M (to x2) (i 2)) qa011 O)))))).


Definition t14 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa100_s (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qa010_s (if_then_else_M (EQ_M (to x1) (i 3)) qa001_s   O) ) )))).
Definition phi3:= phi2 ++ [t14].



(*******************************************phi4*****************************************************)
(************************************************************************************************)
Definition mphi3 := (conv_mylist_listm phi3).
Definition x4 := (f mphi3).
Definition mx3rn3 := (exp (G 0) (m x3) (r 3)).
Definition mx3rn2 := (exp (G 0) (m x3) (r 2)).
Definition mx3rn1 := (exp (G 0) (m x3) (r 1)).

Definition qa210 := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 2) (if_then_else_M (EQ_M (to x4) (i 3)) (grn 3) O) )))))).

Definition qa201 :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 2) O))))))))     .


Definition qa120 :=   (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) acc (if_then_else_M (EQ_M (to x4) (i 3)) (grn 3) O) )))))).

Definition qa111 := (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1)) acc (if_then_else_M (EQ_M (to x4) (i 2)) acc  O))))))).


Definition qa102 := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (to x4) (i 1)) acc (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 2) O )))).

Definition qa021 :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 1)  O )))))))).

Definition qa012 :=   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 1)   (if_then_else_M (EQ_M (to x4) (i 2)) acc O)))).

Definition qa300 := (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 2) (if_then_else_M (EQ_M (to x4) (i 3)) (grn 3) O)))) .

Definition qa030 := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 1) (if_then_else_M (EQ_M (to x4) (i 3)) (grn 3) O)))) .

(********************************************************************************************)
(*******************************************************************************************)
 
Definition qa200_s := (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qa210 (if_then_else_M (EQ_M (to x3) (i 3))  qa201 O))))).

Definition qa110_s := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qa210 (if_then_else_M (EQ_M (to x3) (i 2))  qa120 (if_then_else_M (EQ_M (to x3) (i 3))  qa111 O)))))).


Definition qa101_s :=  (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102 (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qa201
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qa111 O)))))).


Definition qa020_s := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa120 (if_then_else_M (EQ_M (to x3) (i 1)) qa021  O))))).

Definition qa011_s := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012 (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa111 (if_then_else_M (EQ_M (to x3) (i 2)) qa021  O)))))).


 

Definition qa002_s :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa102 (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) qa012 O)))).

(***********************************************************************)


Definition qa100_ss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa200_s  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qa110_s (if_then_else_M (EQ_M (to x2) (i 3)) qa101_s O)))))).


Definition qa010_ss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qa020_s (if_then_else_M (EQ_M (to x2) (i 3))  qa011_s O)))))).

Definition qa001_ss := (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_s  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa101_s (if_then_else_M (EQ_M (to x2) (i 2)) qa011_s O)))))).


Definition t15 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa100_ss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qa010_ss (if_then_else_M (EQ_M (to x1) (i 3)) qa001_ss   O) ) )))).
Definition phi4:= phi3 ++ [t15].



(*******************************************phi5****************************************************************)
(***************************************************************************************************************)


Definition mphi4 := (conv_mylist_listm phi4).
Definition x5 := (f mphi4).
Definition mx4rn4 := (exp (G 0) (m x4) (r 4)).
Definition mx4rn3 := (exp (G 0) (m x4) (r 3)).
Definition mx4rn2 := (exp (G 0) (m x4) (r 2)).
Definition mx4rn1 := (exp (G 0) (m x4) (r 1)).


Definition qa220:=

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1 
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3 

(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3)) (grn 3) O)))))))))))))).



Definition qa211:= (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 3)) acc O)))))))))))).


Definition qa202 :=    (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 2) O) ))))))).

Definition qa121 :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 

 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) acc O)))))))))))).

Definition qa112:=  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) acc (if_then_else_M (EQ_M (to x5) (i 2)) acc  O)))).



Definition qa022 :=   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3 
 (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 1) O)))))))).
 
Definition qa031 :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn3   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn3  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 1) O)))))).

Definition qa130 :=(if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 1)) acc (if_then_else_M (EQ_M (to x5) (i 3)) (grn 3)  O)))).

Definition qa301 :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 2) O)))))).
Definition qa310 := 
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) acc (if_then_else_M (EQ_M (to x5) (i 3)) (grn 3)  O)))).







(*************************************************************************************************)
(*************************************************************************************************)

Definition qa210_s := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qa220 (if_then_else_M (EQ_M (to x4) (i 3)) qa211 O) )))))).

Definition qa201_s :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa202 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa202 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa202
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa301
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa301
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa301 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa211 O))))))))     .


Definition qa120_s :=   (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qa220 (if_then_else_M (EQ_M (to x4) (i 3)) qa121 O) )))))).

Definition qa111_s := (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qa211 (if_then_else_M (EQ_M (to x4) (i 2))  qa121  O))))))).


Definition qa102_s := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (to x4) (i 1)) qa202 (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa112 O )))).

Definition qa021_s :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa031
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa031
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa031
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa121  O )))))))).

Definition qa012_s :=   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa112   (if_then_else_M (EQ_M (to x4) (i 2)) qa022 O)))).

Definition qa300_s := (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa310 (if_then_else_M (EQ_M (to x4) (i 3)) (grn 3) O)))) .

Definition qa030_s := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa130 (if_then_else_M (EQ_M (to x4) (i 3)) qa031 O)))) .

(********************************************************************************************)
(*******************************************************************************************)
 
Definition qa200_ss := (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_s (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qa210_s (if_then_else_M (EQ_M (to x3) (i 3))  qa201_s O))))).

Definition qa110_ss := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qa210_s (if_then_else_M (EQ_M (to x3) (i 2))  qa120_s (if_then_else_M (EQ_M (to x3) (i 3))  qa111_s O)))))).


Definition qa101_ss :=  (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_s (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_s  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qa201_s
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qa111_s O)))))).


Definition qa020_ss := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_s (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa120_s (if_then_else_M (EQ_M (to x3) (i 1)) qa021_s  O))))).

Definition qa011_ss := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_s (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_s (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa111_s (if_then_else_M (EQ_M (to x3) (i 2)) qa021_s  O)))))).


 

Definition qa002_ss :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa102_s (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) qa012_s O)))).

(***********************************************************************)


Definition qa100_sss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa200_ss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qa110_ss (if_then_else_M (EQ_M (to x2) (i 3)) qa101_ss O)))))).


Definition qa010_sss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110_ss (if_then_else_M (EQ_M (to x2) (i 2))  qa020_ss (if_then_else_M (EQ_M (to x2) (i 3))  qa011_ss O)))))).

Definition qa001_sss := (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_ss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa101_ss (if_then_else_M (EQ_M (to x2) (i 2)) qa011_ss O)))))).


Definition t16 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa100_sss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qa010_sss (if_then_else_M (EQ_M (to x1) (i 3)) qa001_sss   O) ) )))).
Definition phi5:= phi4 ++ [t16].


(*******************************************phi6****************************************************************)
(***************************************************************************************************************)


Definition mphi5 := (conv_mylist_listm phi5).
Definition x6 := (f mphi5).
Definition mx5rn4 := (exp (G 0) (m x5) (r 4)).
Definition mx5rn3 := (exp (G 0) (m x5) (r 3)).
Definition mx5rn2 := (exp (G 0) (m x5) (r 2)).
Definition mx5rn1 := (exp (G 0) (m x5) (r 1)).
 
Definition mx5rn5 := (exp (G 0) (m x5) (r 5)).
Definition qa221 :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5 

(********************i2************)
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4



(*****i1****)
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 O)) ))))))))))))))))))))))).

Definition qa212 := (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4 (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (to x6) (i 2)) acc O)))))))))))).

Definition qa122 :=

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) acc O)))))))))))).

Definition qa320 := (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) (grn 3) O)))))))))))).

Definition qa230 := (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) (grn 3) O)))))))))))).

Definition qa131 :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) acc O))))))).

Definition qa311 :=  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5  (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (to x6) (i 2)) acc O))))))).

Definition qa302 := (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  (grn 2) O)).
Definition qa032 :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  (grn 1) O)).
Definition qa023 := (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  (grn 1) O)))))))))))).
Definition  qa113 :=   (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 2)) acc O)))).

(***********************************************************************************************)
(***********************************************************************************************)

Definition qa220_s :=

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa230
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa230
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa320
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa320

(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3))  qa221 O)))))))))))))).



Definition qa211_s := (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3))  qa212
 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa212
   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa212
  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa212
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa311
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa311
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa311
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa311
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa311
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa311
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qa221  O)))))))))))).


Definition qa202_s :=    (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa302
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa302
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa302
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa302
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa302
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa302
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa212 O) ))))))).

Definition qa121_s  :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa122
    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa122
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa122
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa122
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa131
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa131
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa131
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa131
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa131
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa131
     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) qa221 O)))))))))))).

Definition qa112_s :=  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (to x5) (i 1))  qa212 (if_then_else_M (EQ_M (to x5) (i 2))  qa122  O)))).


Definition qa022_s :=   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa032
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa032
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa032
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qa032
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qa032
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qa032
 (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa122 O)))))))).
 
Definition qa031_s :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa032
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa032
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa032
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa032
  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa131 O)))))).

Definition qa130_s :=(if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 1)) qa230 (if_then_else_M (EQ_M (to x5) (i 3)) qa131  O)))).

Definition qa301_s :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa302
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa302
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa302
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa302
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa311 O)))))).
Definition qa310_s := 
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qa320 (if_then_else_M (EQ_M (to x5) (i 3)) qa311  O)))).







(*************************************************************************************************)
(*************************************************************************************************)

Definition qa210_ss := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310_s
 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310_s
  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310_s
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qa220_s (if_then_else_M (EQ_M (to x4) (i 3)) qa211_s O) )))))).

Definition qa201_ss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa202_s
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa202_s
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa202_s
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa301_s
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa301_s
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa301_s 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa211_s O))))))))     .


Definition qa120_ss :=   (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130_s
   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qa220_s (if_then_else_M (EQ_M (to x4) (i 3)) qa121_s O) )))))).

Definition qa111_ss := (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112_s
  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112_s
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112_s
    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qa211_s
 (if_then_else_M (EQ_M (to x4) (i 2))  qa121_s  O))))))).


Definition qa102_ss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (to x4) (i 1)) qa202_s (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa112_s O )))).

Definition qa021_ss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022_s 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022_s
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa031_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa031_s
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa031_s
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa121_s  O )))))))).

Definition qa012_ss :=   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa112_s   (if_then_else_M (EQ_M (to x4) (i 2)) qa022_s O)))).

Definition qa300_ss := (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa310_s (if_then_else_M (EQ_M (to x4) (i 3)) qa301 O)))) .

Definition qa030_ss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa130_s (if_then_else_M (EQ_M (to x4) (i 3)) qa031_s O)))) .

(********************************************************************************************)
(*******************************************************************************************)
 
Definition qa200_sss := (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_ss (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qa210_ss (if_then_else_M (EQ_M (to x3) (i 3))  qa201_ss O))))).

Definition qa110_sss := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qa210_ss (if_then_else_M (EQ_M (to x3) (i 2))  qa120_ss (if_then_else_M (EQ_M (to x3) (i 3))  qa111_ss O)))))).


Definition qa101_sss :=  (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_ss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_ss  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qa201_ss
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qa111_ss O)))))).


Definition qa020_sss := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_ss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa120_ss (if_then_else_M (EQ_M (to x3) (i 1)) qa021_ss  O))))).

Definition qa011_sss := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_ss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_ss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa111_ss (if_then_else_M (EQ_M (to x3) (i 2)) qa021_ss  O)))))).


 

Definition qa002_sss :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa102_ss (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) qa012_ss O)))).

(***********************************************************************)


Definition qa100_ssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa200_sss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qa110_sss (if_then_else_M (EQ_M (to x2) (i 3)) qa101_sss O)))))).


Definition qa010_ssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110_sss (if_then_else_M (EQ_M (to x2) (i 2))  qa020_sss (if_then_else_M (EQ_M (to x2) (i 3))  qa011_sss O)))))).

Definition qa001_ssss := (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_sss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa101_sss (if_then_else_M (EQ_M (to x2) (i 2)) qa011_sss O)))))).


Definition t17 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa100_ssss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qa010_ssss (if_then_else_M (EQ_M (to x1) (i 3)) qa001_ssss   O) ) )))).
Definition phi6:= phi5 ++ [t17].


(******************************phi7*********************************************)
(****************************************************************************)



Definition mphi6 := (conv_mylist_listm phi6).
Definition x7 := (f mphi6).
Definition mx6rn6 := (exp (G 0) (m x6) (r 6)).
Definition mx6rn5 := (exp (G 0) (m x6) (r 5)).
Definition mx6rn4 := (exp (G 0) (m x6) (r 4)).
Definition mx6rn3 := (exp (G 0) (m x6) (r 3)).
Definition mx6rn2 := (exp (G 0) (m x6) (r 2)).
Definition mx6rn1 := (exp (G 0) (m x6) (r 1)).

Definition qa222 := 
 (**i2****)
(if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x5) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5
 (**i1***)

(if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x5) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5
         O)))))))))))))))))))))))))))))).

Definition qa321:= (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) mx6rn6 (****)

(if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x5) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5
  O))))))))))))))))))))).


Definition qa312 := (if_then_else_M (EQ_M (reveal x7) (i 2) ) O (if_then_else_M (EQ_M (to x7) (i 2)) acc O)).

Definition qa231 :=

(if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) mx6rn6

(if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x5) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5 
 O))))))))))))))))))))).

Definition qa132 := (if_then_else_M (EQ_M (reveal x7) (i 1) ) O (if_then_else_M (EQ_M (to x7) (i 1)) acc O)).
Definition qa330  := (if_then_else_M (EQ_M (reveal x7) (i 3) ) O (if_then_else_M (EQ_M (to x7) (i 3)) acc O)).
(*************************************************************************************************)
(************************************************************************************************)

Definition qa221_s :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa222 
(********************i2************)
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa231
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa231
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa231
   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa231
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa231
(*****i1****)
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa321
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa321
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa321
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa321
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa321

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa321

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa321
 O)) ))))))))))))))))))))))).

Definition qa212_s := (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa312
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa312
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa312
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa312
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa312
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa312
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa312
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (to x6) (i 2)) qa222 O)))))))))))).

Definition qa122_s :=

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new)  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa132
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa132
   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa132
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa132
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa132
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa132
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa132
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa132
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa132
 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) qa222 O)))))))))))).

Definition qa320_s := (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330  
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qa321 O)))))))))))).

Definition qa230_s := (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa330
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qa231 O)))))))))))).

Definition qa131_s :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa132
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa132
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) qa231 O))))))).

Definition qa311_s :=  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3))  qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa312 (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (to x6) (i 2)) qa321 O))))))).

Definition qa302_s := (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa312 O)).
Definition qa032_s :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa132 O)).

 
(***********************************************************************************************)
(***********************************************************************************************)

Definition qa220_ss :=

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa230_s
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa230_s
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qa230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qa230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qa230_s
(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3))  qa221_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa320_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa320_s  O))))))))
)))))).



Definition qa211_ss := (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3))  qa212_s
 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa212_s
   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa212_s
  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa212_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa311_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa311_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa311_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa311_s
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa311_s
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa311_s
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qa221_s  O)))))))))))).


Definition qa202_ss :=    (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa302_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa212_s O) ))))))).

Definition qa121_ss  :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa122_s
    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa122_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa122_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa122_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa131_s
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa131_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa131_s
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa131_s
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa131_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa131_s
     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) qa221_s O)))))))))))).

Definition qa112_ss :=  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (to x5) (i 1))  qa212_s (if_then_else_M (EQ_M (to x5) (i 2))  qa122_s  O)))).



Definition qa022_ss :=   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa032_s
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa032_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa032_s
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qa032_s
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qa032_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qa032_s
 (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa122_s O)))))))).

Definition qa031_ss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa032_s
  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa131_s O)))))).

Definition qa130_ss :=(if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 1)) qa230_s (if_then_else_M (EQ_M (to x5) (i 3)) qa131_s  O)))).

Definition qa301_ss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa302_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa302_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa302_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa302_s
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa311_s O)))))).
Definition qa310_ss := 
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qa320_s (if_then_else_M (EQ_M (to x5) (i 3)) qa311_s  O)))).







(*************************************************************************************************)
(*************************************************************************************************)

Definition qa210_sss := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310_ss
  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310_ss
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qa220_ss (if_then_else_M (EQ_M (to x4) (i 3)) qa211_ss O) )))))).

Definition qa201_sss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa202_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa202_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa202_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa301_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa301_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa301_ss 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa211_ss O))))))))     .


Definition qa120_sss :=   (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130_ss
   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qa220_ss (if_then_else_M (EQ_M (to x4) (i 3)) qa121_ss O) )))))).

Definition qa111_sss := (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112_ss
  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112_ss
    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qa211_ss
 (if_then_else_M (EQ_M (to x4) (i 2))  qa121_ss  O))))))).


Definition qa102_sss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (to x4) (i 1)) qa202_ss (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa112_ss O )))).

Definition qa021_sss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022_ss 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022_ss
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa031_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa031_ss
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa031_ss
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa121_ss  O )))))))).

Definition qa012_sss :=   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa112_ss   (if_then_else_M (EQ_M (to x4) (i 2)) qa022_ss O)))).

Definition qa300_sss := (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa310_ss (if_then_else_M (EQ_M (to x4) (i 3)) qa301_ss O)))) .

Definition qa030_sss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa130_ss (if_then_else_M (EQ_M (to x4) (i 3)) qa031_ss O)))) .

(********************************************************************************************)
(*******************************************************************************************)
 
Definition qa200_ssss := (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_sss (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qa210_sss (if_then_else_M (EQ_M (to x3) (i 3))  qa201_sss O))))).

Definition qa110_ssss := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qa210_sss (if_then_else_M (EQ_M (to x3) (i 2))  qa120_sss (if_then_else_M (EQ_M (to x3) (i 3))  qa111_sss O)))))).


Definition qa101_ssss :=  (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_sss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_sss  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qa201_sss
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qa111_sss O)))))).


Definition qa020_ssss := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_sss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa120_sss (if_then_else_M (EQ_M (to x3) (i 1)) qa021_sss  O))))).

Definition qa011_ssss := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_sss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_sss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa111_sss (if_then_else_M (EQ_M (to x3) (i 2)) qa021_sss  O)))))).


 

Definition qa002_ssss :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa102_sss (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) qa012_sss O)))).

(***********************************************************************)


Definition qa100_sssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa200_ssss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qa110_ssss (if_then_else_M (EQ_M (to x2) (i 3)) qa101_ssss O)))))).


Definition qa010_sssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qa020_ssss (if_then_else_M (EQ_M (to x2) (i 3))  qa011_ssss O)))))).

Definition qa001_sssss := (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_ssss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa101_ssss (if_then_else_M (EQ_M (to x2) (i 2)) qa011_ssss O)))))).


Definition t18 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa100_sssss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qa010_sssss (if_then_else_M (EQ_M (to x1) (i 3)) qa001_sssss   O) ) )))).
Definition phi7:= phi6 ++ [t18].

(******************************phi8*********************************************)
(****************************************************************************)

Definition mphi7 := (conv_mylist_listm phi7).
Definition x8 := (f mphi7).
Definition mx7rn7 := (exp (G 0) (m x7) (r 6)).
Definition mx7rn6 := (exp (G 0) (m x7) (r 6)).
Definition mx7rn5 := (exp (G 0) (m x7) (r 5)).
Definition mx7rn4 := (exp (G 0) (m x7) (r 4)).
Definition mx7rn3 := (exp (G 0) (m x7) (r 3)).
Definition mx7rn2 := (exp (G 0) (m x7) (r 2)).
Definition mx7rn1 := (exp (G 0) (m x7) (r 1)).
Definition qa322 := 
(if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x5) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5

(if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x7) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x7) new)) & (EQ_M (act x1) new) mx7rn1
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x7) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x7) new)) & (EQ_M (act x2) new) mx7rn2
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x7) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x7) new)) & (EQ_M (act x3) new) mx7rn3
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x7) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x7) new)) & (EQ_M (act x4) new) mx7rn4
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x7) (i 2)) & (EQ_M (to x5) (i 2))& (notb (EQ_M (act x7) new)) & (EQ_M (act x5) new) mx7rn5
 (if_then_else_M (EQ_M (reveal x8) (i 2)) & (EQ_M (to x7) (i 2)) & (EQ_M (to x6) (i 2))& (notb (EQ_M (act x7) new)) & (EQ_M (act x5) new) mx7rn6 O))))))))))))))))))))).

Definition qa331 := (if_then_else_M (EQ_M (reveal x8) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x8) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x8) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M (EQ_M (reveal x8) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4
  (if_then_else_M (EQ_M (reveal x8) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5
  (if_then_else_M (EQ_M (reveal x8) (i 3)) & (EQ_M (to x6) (i 3)) mx6rn6
(if_then_else_M (EQ_M (reveal x8) (i 3)) & (EQ_M (to x7) (i 3)) mx7rn7 O))))))).
Definition qa232 := 
(if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x5) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5

(if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x7) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x7) new)) & (EQ_M (act x1) new) mx7rn1
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x7) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x7) new)) & (EQ_M (act x2) new) mx7rn2
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x7) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x7) new)) & (EQ_M (act x3) new) mx7rn3
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x7) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x7) new)) & (EQ_M (act x4) new) mx7rn4
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x7) (i 1)) & (EQ_M (to x5) (i 1))& (notb (EQ_M (act x7) new)) & (EQ_M (act x5) new) mx7rn5
 (if_then_else_M (EQ_M (reveal x8) (i 1)) & (EQ_M (to x7) (i 1)) & (EQ_M (to x6) (i 1))& (notb (EQ_M (act x7) new)) & (EQ_M (act x5) new) mx7rn6 O))))))))))))))))))))).

(************************************************************************************************************)


Definition qa222_s :=


   (**i2****)
(if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa232
  (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x5) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) qa232


  (**i1***)(if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa322
  (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x5) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) qa322
       O)))))))))))))))))))))))))))))).

Definition qa321_s:= (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) qa322
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3))  qa322
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) qa322
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) qa322
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) qa322 (****)

(if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa331
  (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x5) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) qa331
  O))))))))))))))))))))).


Definition qa312_s := (if_then_else_M (EQ_M (reveal x7) (i 2) ) O (if_then_else_M (EQ_M (to x7) (i 2)) qa322 O)).

Definition qa231_s :=

(if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3)) qa232
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) qa232
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) qa232
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) qa232

(if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa331
  (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) qa331
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x5) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) qa331 
 O))))))))))))))))))))).

Definition qa132_s := (if_then_else_M (EQ_M (reveal x7) (i 1) ) O (if_then_else_M (EQ_M (to x7) (i 1)) qa232 O)).
Definition qa330_s  := (if_then_else_M (EQ_M (reveal x7) (i 3) ) O (if_then_else_M (EQ_M (to x7) (i 3)) qa331 O)).
(*************************************************************************************************)
(************************************************************************************************)

Definition qa221_ss :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa222_s 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) qa222_s 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa222_s 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa222_s 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa222_s 
(********************i2************)
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa231_s
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa231_s
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa231_s
   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa231_s
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa231_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa231_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa231_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa231_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa231_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa231_s
(*****i1****)
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa321_s
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa321_s
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa321_s
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa321_s
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa321_s

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa321_s

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa321_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa321_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa321_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa321_s
 O)) ))))))))))))))))))))))).

Definition qa212_ss := (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa312_s
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa312_s
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa312_s
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa312_s
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa312_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa312_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa312_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa312_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa312_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa312_s
 (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (to x6) (i 2)) qa222_s O)))))))))))).

Definition qa122_ss :=

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new)  qa132_s
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa132_s
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa132_s
   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa132_s
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa132_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa132_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa132_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa132_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa132_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa132_s
 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) qa222_s O)))))))))))).

Definition qa320_ss := (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330_s
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa330_s
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330_s  
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330_s
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330_s (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qa321_s O)))))))))))).

Definition qa230_ss := (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330_s
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa330_s
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330_s
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330_s
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330_s
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330_s
 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qa231_s O)))))))))))).

Definition qa131_ss :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa132_s
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa132_s
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3))  qa132_s
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3))  qa132_s
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3))  qa132_s
 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) qa231_s O))))))).

Definition qa311_ss :=  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3))  qa312_s
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa312_s
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa312_s
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa312_s
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa312_s (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (to x6) (i 2)) qa321_s O))))))).

Definition qa302_ss := (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa312_s O)).
Definition qa032_ss :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa132_s O)).

 
(***********************************************************************************************)
(***********************************************************************************************)

Definition qa220_sss :=

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa230_ss
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa230_ss
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa230_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qa230_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qa230_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qa230_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa320_ss
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa320_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa320_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa320_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa320_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa320_ss

(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3))  qa221_ss O)))))))))))))).



Definition qa211_sss := (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3))  qa212_ss
 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa212_ss
   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa212_ss
  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa212_ss
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa311_ss
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa311_ss
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa311_ss
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa311_ss
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa311_ss
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa311_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qa221_ss  O)))))))))))).


Definition qa202_sss :=    (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa302_ss
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa302_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa302_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa302_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa302_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa302_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa212_ss O) ))))))).

Definition qa121_sss  :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa122_ss
    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa122_ss
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa122_ss
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa122_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa131_ss
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa131_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa131_ss
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa131_ss
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa131_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa131_ss
     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) qa221_ss O)))))))))))).

Definition qa112_sss :=  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (to x5) (i 1))  qa212_ss (if_then_else_M (EQ_M (to x5) (i 2))  qa122_ss  O)))).



Definition qa022_sss :=   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa032_ss
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa032_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa032_ss
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qa032_ss
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qa032_ss
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qa032_ss
 (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa122_ss O)))))))).

Definition qa031_sss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa032_ss
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa032_ss
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa032_ss
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa032_ss
  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa131_ss O)))))).

Definition qa130_sss :=(if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 1)) qa230_ss (if_then_else_M (EQ_M (to x5) (i 3)) qa131_ss  O)))).

Definition qa301_sss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa302_ss
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa302_ss
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa302_ss
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa302_ss
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa311_ss O)))))).
Definition qa310_sss := 
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qa320_ss (if_then_else_M (EQ_M (to x5) (i 3)) qa311_ss  O)))).







(*************************************************************************************************)
(*************************************************************************************************)

Definition qa210_ssss := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310_sss
 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310_sss
  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310_sss
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qa220_sss (if_then_else_M (EQ_M (to x4) (i 3)) qa211_sss O) )))))).

Definition qa201_ssss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa202_sss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa202_sss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa202_sss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa301_sss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa301_sss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa301_sss 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa211_sss O))))))))     .


Definition qa120_ssss :=   (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130_sss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130_sss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130_sss
   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qa220_sss (if_then_else_M (EQ_M (to x4) (i 3)) qa121_sss O) )))))).

Definition qa111_ssss := (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112_sss
  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112_sss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112_sss
    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qa211_sss
 (if_then_else_M (EQ_M (to x4) (i 2))  qa121_sss  O))))))).


Definition qa102_ssss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (to x4) (i 1)) qa202_sss (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa112_sss O )))).

Definition qa021_ssss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022_sss 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022_sss
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022_sss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa031_sss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa031_sss
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa031_sss
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa121_sss  O )))))))).

Definition qa012_ssss :=   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa112_sss   (if_then_else_M (EQ_M (to x4) (i 2)) qa022_sss O)))).

Definition qa300_ssss := (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa310_sss (if_then_else_M (EQ_M (to x4) (i 3)) qa301 O)))) .

Definition qa030_ssss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qa130_sss (if_then_else_M (EQ_M (to x4) (i 3)) qa031_sss O)))) .

(********************************************************************************************)
(*******************************************************************************************)
 
Definition qa200_sssss := (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_ssss (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qa210_ssss (if_then_else_M (EQ_M (to x3) (i 3))  qa201_ssss O))))).

Definition qa110_sssss := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qa210_ssss (if_then_else_M (EQ_M (to x3) (i 2))  qa120_ssss (if_then_else_M (EQ_M (to x3) (i 3))  qa111_ssss O)))))).


Definition qa101_sssss :=  (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_ssss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_ssss  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qa201_ssss
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qa111_ssss O)))))).


Definition qa020_sssss := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_ssss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa120_ssss (if_then_else_M (EQ_M (to x3) (i 1)) qa021_ssss  O))))).

Definition qa011_sssss := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_ssss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_ssss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa111_ssss (if_then_else_M (EQ_M (to x3) (i 2)) qa021_ssss  O)))))).


 

Definition qa002_sssss :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa102_ssss (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) qa012_ssss O)))).

(***********************************************************************)


Definition qa100_ssssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa200_sssss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qa110_sssss (if_then_else_M (EQ_M (to x2) (i 3)) qa101_sssss O)))))).


Definition qa010_ssssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qa020_sssss (if_then_else_M (EQ_M (to x2) (i 3))  qa011_sssss O)))))).

Definition qa001_ssssss := (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_sssss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qa101_sssss (if_then_else_M (EQ_M (to x2) (i 2)) qa011_sssss O)))))).


Definition t19 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa100_ssssss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qa010_ssssss (if_then_else_M (EQ_M (to x1) (i 3)) qa001_ssssss   O) ) )))).
Definition phi8:= phi7 ++ [t19].



(******************************************************************************************************************************************************)
(******************************************************************************************************************************************************)
(***********************protocol Pi2 : add transitions to qa2001************)
(***************************************************************************)

(*

Definition phi21 := phi1.
Definition phi22 := phi2.
Definition phi23 := phi3.
*)
(*******alpha = 1, beta =3 *************)



Definition qb201 :=  (if_then_else_M (EQ_M (reveal  x4) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M (EQ_M (reveal  x4) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4)  
    (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 2) O))))))))))   .

(*********alpha = 2, beta = 3***************)

 
Definition qb021 :=  (if_then_else_M (EQ_M (reveal  x4) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M (EQ_M (reveal  x4) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4)  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 1)  O )))))))) )).


Definition qb200_s :=


(if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qa210 (if_then_else_M (EQ_M (to x3) (i 3))  qb201 O))))).

Definition qb101_s := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102 (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qb201
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qa111 O)))))).

Definition qb020_s := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa120 (if_then_else_M (EQ_M (to x3) (i 1)) qb021  O))))).


Definition qb100_ss :=

 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qb200_s  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qa110_s (if_then_else_M (EQ_M (to x2) (i 3)) qb101_s O)))))).



  

Definition qb010_ss := 

(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qb020_s (if_then_else_M (EQ_M (to x2) (i 3))  qa011_s O)))))).


 
Definition t25 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qb100_ss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qb010_ss (if_then_else_M (EQ_M (to x1) (i 3)) qa001_ss   O) ) )))).
Definition phi24:= phi3 ++ [t25].


(*************************************phi25*****************************************)

Definition qb211:=  (if_then_else_M (EQ_M (reveal  x5) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M (EQ_M (reveal  x5) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 3)) acc O))))))))))))))  .


Definition qb121 :=   (if_then_else_M (EQ_M (reveal  x5) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M (EQ_M (reveal  x5) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 

 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) acc O)))))))))))))).

(***************************************_s*****************************)
Definition qb210_s := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qa220 (if_then_else_M (EQ_M (to x4) (i 3)) qb211 O) )))))).



Definition qb201_s :=

 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa202 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa202 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa202
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa301
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa301
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa301 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qb211 O)))))))).     



Definition qb120_s := 

(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qa220 (if_then_else_M (EQ_M (to x4) (i 3)) qb121 O) )))))).


Definition qb111_s :=
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qb211 (if_then_else_M (EQ_M (to x4) (i 2))  qb121  O))))))).

 

Definition qb021_s :=

 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa031
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa031
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa031
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qb121  O )))))))).


(***************_SS*************************)

Definition qb200_ss :=
 (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_s (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qb210_s (if_then_else_M (EQ_M (to x3) (i 3))  qb201_s O))))).


Definition qb110_ss :=
(if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qb210_s (if_then_else_M (EQ_M (to x3) (i 2))  qb120_s (if_then_else_M (EQ_M (to x3) (i 3))  qb111_s O)))))).





Definition qb101_ss := 
(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_s (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_s  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qb201_s
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qb111_s O)))))).



Definition qb020_ss := 

(if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_s (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qb120_s (if_then_else_M (EQ_M (to x3) (i 1)) qb021_s  O))))).


Definition qb011_ss :=

(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_s (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_s (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qb111_s (if_then_else_M (EQ_M (to x3) (i 2)) qb021_s  O)))))).

(********************************************************)

Definition qb100_sss := 
(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qb200_ss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qb110_ss (if_then_else_M (EQ_M (to x2) (i 3)) qb101_ss O)))))).



Definition qb010_sss := 

 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qb110_ss (if_then_else_M (EQ_M (to x2) (i 2))  qb020_ss (if_then_else_M (EQ_M (to x2) (i 3))  qb011_ss O)))))).


Definition qb001_sss := 
(if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_ss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qb101_ss (if_then_else_M (EQ_M (to x2) (i 2)) qb011_ss O)))))).


Definition t26 := 
msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qb100_sss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qb010_sss (if_then_else_M (EQ_M (to x1) (i 3)) qb001_sss   O) ) )))).



Definition phi25:= phi24 ++ [t26].



(*********************************phi26****************)
(*******alpha =2, beta =3********************)
 
Definition qb221 :=  (if_then_else_M (EQ_M (reveal  x6) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4)



 (if_then_else_M (EQ_M (reveal  x6) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4)
(if_then_else_M (EQ_M (reveal  x6) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4)
 (if_then_else_M (EQ_M (reveal  x6) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4)  

(if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5 

(********************i2************)
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
(*****i1****)
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 O)) ))))))))))))))))))))))))))).


Definition qb220_s :=
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa230
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa230
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qa230
(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3))  qb221

 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa320
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa320
 O)))))))))))))).






Definition qb121_s := 


 (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa122
    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa122
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa122
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa122
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa131
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa131
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa131
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa131
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa131
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa131
     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) qb221 O)))))))))))).

Definition qb210_ss := 

(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310_s
 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310_s
  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310_s
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qb220_s (if_then_else_M (EQ_M (to x4) (i 3)) qa211_s O) )))))).


Definition qb120_ss := 

(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130_s
   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qb220_s (if_then_else_M (EQ_M (to x4) (i 3)) qb121_s O) )))))).



Definition qb111_ss :=

(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112_s
  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112_s
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112_s
    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qa211_s
 (if_then_else_M (EQ_M (to x4) (i 2))  qb121_s  O))))))).

(*********************************************************************************)

Definition qb200_sss :=

(if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_ss (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qb210_ss (if_then_else_M (EQ_M (to x3) (i 3))  qa201_ss O))))).


Definition qb110_sss :=
 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qb210_ss (if_then_else_M (EQ_M (to x3) (i 2))  qb120_ss (if_then_else_M (EQ_M (to x3) (i 3))  qb111_ss O)))))).




Definition qb101_sss := 

(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_ss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_ss  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qa201_ss
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qb111_ss O)))))).



Definition qb020_sss :=

(if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_ss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qb120_ss (if_then_else_M (EQ_M (to x3) (i 1)) qa021_ss  O))))).



Definition qb011_sss :=

(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_ss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_ss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qb111_ss (if_then_else_M (EQ_M (to x3) (i 2)) qa021_ss  O)))))).


(*************************************************)
Definition qb100_ssss :=
(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qb200_sss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qb110_sss (if_then_else_M (EQ_M (to x2) (i 3)) qb101_sss O)))))).



Definition qb010_ssss := 
(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qb110_sss (if_then_else_M (EQ_M (to x2) (i 2))  qb020_sss (if_then_else_M (EQ_M (to x2) (i 3))  qb011_sss O)))))).



Definition qb001_ssss :=
(if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_sss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qb101_sss (if_then_else_M (EQ_M (to x2) (i 2)) qb011_sss O)))))).




Definition t27 :=
msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qb100_ssss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qb010_ssss (if_then_else_M (EQ_M (to x1) (i 3)) qb001_ssss   O) ) )))).



Definition phi26 := phi25 ++ [t27].
(*********************************************************************************)
(**********************phi27******************************************************)

(*******alpha=2, beta = 3*****************)
Definition qb321 :=   (if_then_else_M (EQ_M (reveal  x7) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M (EQ_M (reveal  x7) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) mx6rn6 (****)

(if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x5) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5
  O))))))))))))))))))))))).

(********alpha=1, beta =3**************)
Definition qb231 :=   (if_then_else_M (EQ_M (reveal  x7) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M (EQ_M (reveal  x7) (i 1) ) &  (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) mx6rn6

(if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x5) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5 
 O))))))))))))))))))))))).

(********************************************************************************************)


Definition qb221_s :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa222 
(********************i2************)
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qb231
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qb231
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qb231
   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qb231
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qb231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qb231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qb231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qb231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qb231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qb231
(*****i1****)
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qb321
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qb321
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qb321
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qb321
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qb321

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qb321

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qb321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qb321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qb321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qb321
 O)) ))))))))))))))))))))))).

Definition qb320_s := (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330  
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qb321 O)))))))))))).

Definition qb230_s := (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa330
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qb231 O)))))))))))).

Definition qb131_s :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa132
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa132
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) qb231 O))))))).


Definition qb311_s :=  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3))  qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa312 (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (to x6) (i 2)) qb321 O))))))).
(***********************************************************************)
(***********************************************************************)



Definition qb220_ss :=
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qb230_s
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qb230_s
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qb230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qb230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qb230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qb230_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qb320_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qb320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qb320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qb320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qb320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qb320_s

(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3))  qb221_s O)))))))))))))).



Definition qb211_ss := (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3))  qa212_s
 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa212_s
   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa212_s
  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa212_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qb311_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qb311_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qb311_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qb311_s
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qb311_s
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qb311_s
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qb221_s  O)))))))))))).


Definition qb202_ss :=    (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa302_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa212_s O) ))))))).

Definition qb121_ss  :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa122_s
    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa122_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa122_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa122_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qb131_s
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qb131_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qb131_s
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qb131_s
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qb131_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qb131_s
     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) qb221_s O)))))))))))).



Definition qb031_ss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa032_s
  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qb131_s O)))))).

Definition qb130_ss :=(if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 1)) qb230_s (if_then_else_M (EQ_M (to x5) (i 3)) qb131_s  O)))).

Definition qb301_ss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa302_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa302_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa302_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa302_s
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qb311_s O)))))).
Definition qb310_ss := 
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qb320_s (if_then_else_M (EQ_M (to x5) (i 3)) qb311_s  O)))).

(*************************************************************************************************)
(*************************************************************************************************)

Definition qb210_sss := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qb310_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qb310_ss
  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qb310_ss
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qb220_ss (if_then_else_M (EQ_M (to x4) (i 3)) qb211_ss O) )))))).

Definition qb201_sss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qb202_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qb202_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qb202_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qb301_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qb301_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qb301_ss 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qb211_ss O))))))))     .


Definition qb120_sss :=   (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qb130_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qb130_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qb130_ss
   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qb220_ss (if_then_else_M (EQ_M (to x4) (i 3)) qb121_ss O) )))))).

Definition qb111_sss := (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112_ss
  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112_ss
    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qb211_ss
 (if_then_else_M (EQ_M (to x4) (i 2))  qb121_ss  O))))))).


Definition qb102_sss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (to x4) (i 1)) qb202_ss (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa112_ss O )))).

Definition qb021_sss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022_ss 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022_ss
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qb031_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qb031_ss
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qb031_ss
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qb121_ss  O )))))))).


Definition qb300_sss := (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qb310_ss (if_then_else_M (EQ_M (to x4) (i 3)) qb301_ss O)))) .

Definition qb030_sss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qb130_ss (if_then_else_M (EQ_M (to x4) (i 3)) qb031_ss O)))) .
(********************************************************************************************)
(*******************************************************************************************)
 
Definition qb200_ssss := (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qb300_sss (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qb210_sss (if_then_else_M (EQ_M (to x3) (i 3))  qb201_sss O))))).

Definition qb110_ssss := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qb210_sss (if_then_else_M (EQ_M (to x3) (i 2))  qb120_sss (if_then_else_M (EQ_M (to x3) (i 3))  qb111_sss O)))))).


Definition qb101_ssss :=  (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qb102_sss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qb102_sss  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qb201_sss
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qb111_sss O)))))).


Definition qb020_ssss := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qb030_sss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qb120_sss (if_then_else_M (EQ_M (to x3) (i 1)) qb021_sss  O))))).

Definition qb011_ssss := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_sss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_sss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qb111_sss (if_then_else_M (EQ_M (to x3) (i 2)) qb021_sss  O)))))).


 

Definition qb002_ssss :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qb102_sss (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) qa012_sss O)))).



(***********************************************************************)


Definition qb100_sssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qb200_ssss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qb110_ssss (if_then_else_M (EQ_M (to x2) (i 3)) qb101_ssss O)))))).


Definition qb010_sssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qb020_ssss (if_then_else_M (EQ_M (to x2) (i 3))  qb011_ssss O)))))).

Definition qb001_sssss := (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qb002_ssss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qb101_ssss (if_then_else_M (EQ_M (to x2) (i 2)) qb011_ssss O)))))).


Definition t28 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qb100_sssss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qb010_sssss (if_then_else_M (EQ_M (to x1) (i 3)) qb001_sssss   O) ) )))).
Definition phi27:= phi26 ++ [t28].
(*********************************)
Definition phi28 := phi27 ++ [t19].
(************************************************************************************)
(************************************************************************************)
(************************Protocol Pi2'': replace the output grn4 by mx12rn2 , mx13rn1 in the term qb2001 in Pi2**********)
(************************************************************************************************************************)

(*

Definition phi31 := phi1.
Definition phi32 := phi2.
Definition phi33 := phi3.
*)
(*******alpha = 1, beta =3 *************)



Definition qc201 :=  (if_then_else_M (EQ_M (reveal  x4) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx2rn2 (if_then_else_M (EQ_M (reveal  x4) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx3rn1     (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 2) O))))))))))   .

(*********alpha = 2, beta = 3***************)

 
Definition qc021 :=  (if_then_else_M (EQ_M (reveal  x4) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx2rn2 (if_then_else_M (EQ_M (reveal  x4) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx3rn1  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 1)  O )))))))) )).


Definition qc200_s :=


(if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qa210 (if_then_else_M (EQ_M (to x3) (i 3))  qc201 O))))).

Definition qc101_s := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102 (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qc201
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qa111 O)))))).

Definition qc020_s := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa120 (if_then_else_M (EQ_M (to x3) (i 1)) qc021  O))))).


Definition qc100_ss :=

 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qc200_s  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qa110_s (if_then_else_M (EQ_M (to x2) (i 3)) qc101_s O)))))).



  

Definition qc010_ss := 

(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qc020_s (if_then_else_M (EQ_M (to x2) (i 3))  qa011_s O)))))).


 
Definition t35 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qc100_ss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qc010_ss (if_then_else_M (EQ_M (to x1) (i 3)) qa001_ss   O) ) )))).
Definition phi34:= phi3 ++ [t35].


(*************************************phi35*****************************************)

Definition qc211:=  (if_then_else_M (EQ_M (reveal  x5) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx2rn2 (if_then_else_M (EQ_M (reveal  x5) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx3rn1 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 3)) acc O))))))))))))))  .


Definition qc121 :=   (if_then_else_M (EQ_M (reveal  x4) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx2rn2 (if_then_else_M (EQ_M (reveal  x4) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx3rn1 (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 

 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) acc O)))))))))))))).

(***************************************_s*****************************)
Definition qc210_s := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qa220 (if_then_else_M (EQ_M (to x4) (i 3)) qc211 O) )))))).



Definition qc201_s :=

 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa202 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa202 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa202
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa301
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa301
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa301 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qc211 O)))))))).     



Definition qc120_s := 

(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qa220 (if_then_else_M (EQ_M (to x4) (i 3)) qc121 O) )))))).


Definition qc111_s :=
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qc211 (if_then_else_M (EQ_M (to x4) (i 2))  qc121  O))))))).

 

Definition qc021_s :=

 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa031
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa031
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa031
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qc121  O )))))))).


(***************_SS*************************)

Definition qc200_ss :=
 (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_s (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qc210_s (if_then_else_M (EQ_M (to x3) (i 3))  qc201_s O))))).


Definition qc110_ss :=
(if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qc210_s (if_then_else_M (EQ_M (to x3) (i 2))  qc120_s (if_then_else_M (EQ_M (to x3) (i 3))  qc111_s O)))))).





Definition qc101_ss := 
(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_s (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_s  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qc201_s
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qc111_s O)))))).



Definition qc020_ss := 

(if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_s (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qc120_s (if_then_else_M (EQ_M (to x3) (i 1)) qc021_s  O))))).


Definition qc011_ss :=

(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_s (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_s (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qc111_s (if_then_else_M (EQ_M (to x3) (i 2)) qc021_s  O)))))).

(********************************************************)

Definition qc100_sss := 
(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qc200_ss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qc110_ss (if_then_else_M (EQ_M (to x2) (i 3)) qc101_ss O)))))).



Definition qc010_sss := 

 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qc110_ss (if_then_else_M (EQ_M (to x2) (i 2))  qc020_ss (if_then_else_M (EQ_M (to x2) (i 3))  qc011_ss O)))))).


Definition qc001_sss := 
(if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_ss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qc101_ss (if_then_else_M (EQ_M (to x2) (i 2)) qc011_ss O)))))).


Definition t36 := 
msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qc100_sss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qc010_sss (if_then_else_M (EQ_M (to x1) (i 3)) qc001_sss   O) ) )))).



Definition phi35:= phi34 ++ [t36].



(*********************************phi36****************)
(*******alpha =2, beta =3********************)
 
Definition qc221 :=  (if_then_else_M (EQ_M (reveal  x6) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx2rn2
 (if_then_else_M (EQ_M (reveal  x6) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx3rn1 
 (if_then_else_M (EQ_M (reveal  x6) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx2rn2
 (if_then_else_M (EQ_M (reveal  x6) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx3rn1



(if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5 
(********************i2************)
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
(*****i1****)
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 O)) ))))))))))))))))))))))))))).


Definition qc220_s :=

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa230
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa230
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa320
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa320

(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3))  qc221 O)))))))))))))).






Definition qc121_s := 


 (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa122
    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa122
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa122
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa122
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa131
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa131
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa131
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa131
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa131
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa131
     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) qc221 O)))))))))))).

Definition qc210_ss := 

(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310_s
 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310_s
  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310_s
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qc220_s (if_then_else_M (EQ_M (to x4) (i 3)) qa211_s O) )))))).


Definition qc120_ss := 

(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130_s
   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qc220_s (if_then_else_M (EQ_M (to x4) (i 3)) qc121_s O) )))))).



Definition qc111_ss :=

(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112_s
  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112_s
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112_s
    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qa211_s
 (if_then_else_M (EQ_M (to x4) (i 2))  qc121_s  O))))))).

(*********************************************************************************)

Definition qc200_sss :=

(if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_ss (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qc210_ss (if_then_else_M (EQ_M (to x3) (i 3))  qa201_ss O))))).


Definition qc110_sss :=
 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qc210_ss (if_then_else_M (EQ_M (to x3) (i 2))  qc120_ss (if_then_else_M (EQ_M (to x3) (i 3))  qc111_ss O)))))).




Definition qc101_sss := 

(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_ss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_ss  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qa201_ss
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qc111_ss O)))))).



Definition qc020_sss :=

(if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_ss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qc120_ss (if_then_else_M (EQ_M (to x3) (i 1)) qa021_ss  O))))).



Definition qc011_sss :=

(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_ss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_ss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qc111_ss (if_then_else_M (EQ_M (to x3) (i 2)) qa021_ss  O)))))).


(*************************************************)
Definition qc100_ssss :=
(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qc200_sss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qc110_sss (if_then_else_M (EQ_M (to x2) (i 3)) qc101_sss O)))))).



Definition qc010_ssss := 
(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qc110_sss (if_then_else_M (EQ_M (to x2) (i 2))  qc020_sss (if_then_else_M (EQ_M (to x2) (i 3))  qc011_sss O)))))).



Definition qc001_ssss :=
(if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_sss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qc101_sss (if_then_else_M (EQ_M (to x2) (i 2)) qc011_sss O)))))).




Definition t37 :=
msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qc100_ssss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qc010_ssss (if_then_else_M (EQ_M (to x1) (i 3)) qc001_ssss   O) ) )))).



Definition phi36 := phi35 ++ [t37].

(*********************************************************************************)
(**********************phi37******************************************************)

(*******alpha=2, beta = 3*****************)
Definition qc321 :=   (if_then_else_M (EQ_M (reveal  x7) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx2rn2 (if_then_else_M (EQ_M (reveal  x7) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx3rn1 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) mx6rn6 (****)

(if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x5) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5
  O))))))))))))))))))))))).

(********alpha=1, beta =3**************)
Definition qc231 :=   (if_then_else_M (EQ_M (reveal  x7) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx2rn2 (if_then_else_M (EQ_M (reveal  x7) (i 1) ) &  (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx3rn1 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) mx6rn6

(if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x5) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5 
 O))))))))))))))))))))))).

(********************************************************************************************)


Definition qc221_s :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa222 

(********************i2************)
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qc231
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qc231
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qc231
   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qc231
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qc231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qc231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qc231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qc231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qc231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qc231

(*****i1****)
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qc321
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qc321
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qc321
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qc321
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qc321

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qc321

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qc321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qc321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qc321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qc321
 O)) ))))))))))))))))))))))).

Definition qc320_s := (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330  
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qc321 O)))))))))))).

Definition qc230_s := (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa330
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qc231 O)))))))))))).

Definition qc131_s :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa132
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa132
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) qc231 O))))))).


Definition qc311_s :=  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3))  qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa312 (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (to x6) (i 2)) qc321 O))))))).
(***********************************************************************)
(***********************************************************************)



Definition qc220_ss :=

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qc230_s
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qc230_s
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qc230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qc230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qc230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qc230_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qc320_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qc320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qc320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qc320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qc320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qc320_s

(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3))  qc221_s O)))))))))))))).



Definition qc211_ss := (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3))  qa212_s
 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa212_s
   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa212_s
  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa212_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qc311_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qc311_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qc311_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qc311_s
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qc311_s
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qc311_s
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qc221_s  O)))))))))))).


Definition qc202_ss :=    (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa302_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa212_s O) ))))))).

Definition qc121_ss  :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa122_s
    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa122_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa122_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa122_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qc131_s
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qc131_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qc131_s
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qc131_s
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qc131_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qc131_s
     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) qc221_s O)))))))))))).



Definition qc031_ss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa032_s
  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qc131_s O)))))).

Definition qc130_ss :=(if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 1)) qc230_s (if_then_else_M (EQ_M (to x5) (i 3)) qc131_s  O)))).

Definition qc301_ss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa302_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa302_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa302_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa302_s
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qc311_s O)))))).
Definition qc310_ss := 
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qc320_s (if_then_else_M (EQ_M (to x5) (i 3)) qc311_s  O)))).

(*************************************************************************************************)
(*************************************************************************************************)

Definition qc210_sss := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qc310_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qc310_ss
  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qc310_ss
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qc220_ss (if_then_else_M (EQ_M (to x4) (i 3)) qc211_ss O) )))))).

Definition qc201_sss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qc202_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qc202_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qc202_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qc301_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qc301_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qc301_ss 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qc211_ss O))))))))     .


Definition qc120_sss :=   (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qc130_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qc130_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qc130_ss
   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qc220_ss (if_then_else_M (EQ_M (to x4) (i 3)) qc121_ss O) )))))).

Definition qc111_sss := (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112_ss
  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112_ss
    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qc211_ss
 (if_then_else_M (EQ_M (to x4) (i 2))  qc121_ss  O))))))).


Definition qc102_sss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (to x4) (i 1)) qc202_ss (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa112_ss O )))).

Definition qc021_sss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022_ss 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022_ss
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qc031_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qc031_ss
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qc031_ss
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qc121_ss  O )))))))).


Definition qc300_sss := (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qc310_ss (if_then_else_M (EQ_M (to x4) (i 3)) qc301_ss O)))) .

Definition qc030_sss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qc130_ss (if_then_else_M (EQ_M (to x4) (i 3)) qc031_ss O)))) .
(********************************************************************************************)
(*******************************************************************************************)
 
Definition qc200_ssss := (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qc300_sss (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qc210_sss (if_then_else_M (EQ_M (to x3) (i 3))  qc201_sss O))))).

Definition qc110_ssss := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qc210_sss (if_then_else_M (EQ_M (to x3) (i 2))  qc120_sss (if_then_else_M (EQ_M (to x3) (i 3))  qc111_sss O)))))).


Definition qc101_ssss :=  (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qc102_sss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qc102_sss  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qc201_sss
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qc111_sss O)))))).


Definition qc020_ssss := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qc030_sss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qc120_sss (if_then_else_M (EQ_M (to x3) (i 1)) qc021_sss  O))))).

Definition qc011_ssss := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_sss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_sss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qc111_sss (if_then_else_M (EQ_M (to x3) (i 2)) qc021_sss  O)))))).


 

Definition qc002_ssss :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qc102_sss (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) qa012_sss O)))).



(***********************************************************************)


Definition qc100_sssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qc200_ssss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qc110_ssss (if_then_else_M (EQ_M (to x2) (i 3)) qc101_ssss O)))))).


Definition qc010_sssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qc020_ssss (if_then_else_M (EQ_M (to x2) (i 3))  qc011_ssss O)))))).

Definition qc001_sssss := (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qc002_ssss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qc101_ssss (if_then_else_M (EQ_M (to x2) (i 2)) qc011_ssss O)))))).


Definition t38 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qc100_sssss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qc010_sssss (if_then_else_M (EQ_M (to x1) (i 3)) qc001_sssss   O) ) )))).
Definition phi37:= phi36 ++ [t38].
(*********************************)
Definition phi38 := phi37 ++ [t19].


(************************************************************************************)
(************************************************************************************)
(************************Protocol Pi2': replace the output grn4 by grn21 in Pi2**********)
(************************************************************************************************************************)

Definition grn21:= (exp (G 0) (exp (G 0) (g 0) (r 2)) (r 1)).

Definition phi41 := phi1.
Definition phi42 := phi2.
Definition phi43 := phi3.

(*******alpha = 1, beta =3 *************)



Definition qd201 :=  (if_then_else_M (EQ_M (reveal  x4) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M (EQ_M (reveal  x4) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21    (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 1)) mx1rn1 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 1)) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 1)) mx3rn3
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 2) O))))))))))   .

(*********alpha = 2, beta = 3***************)

 
Definition qd021 :=  (if_then_else_M (EQ_M (reveal  x4) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M (EQ_M (reveal  x4) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 1)  O )))))))) )).


Definition qd200_s :=


(if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qa210 (if_then_else_M (EQ_M (to x3) (i 3))  qd201 O))))).

Definition qd101_s := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102 (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qd201
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qa111 O)))))).

Definition qd020_s := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qa120 (if_then_else_M (EQ_M (to x3) (i 1)) qd021  O))))).


Definition qd100_ss :=

 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qd200_s  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qa110_s (if_then_else_M (EQ_M (to x2) (i 3)) qd101_s O)))))).



  

Definition qd010_ss := 

(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qd020_s (if_then_else_M (EQ_M (to x2) (i 3))  qa011_s O)))))).


 
Definition t45 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qd100_ss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qd010_ss (if_then_else_M (EQ_M (to x1) (i 3)) qa001_ss   O) ) )))).
Definition phi44:= phi43 ++ [t45].


(*************************************phi45*****************************************)

Definition qd211:=  (if_then_else_M (EQ_M (reveal  x5) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M (EQ_M (reveal  x5) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 3)) acc O))))))))))))))  .


Definition qd121 :=   (if_then_else_M (EQ_M (reveal  x4) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M (EQ_M (reveal  x4) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 

 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) acc O)))))))))))))).

(***************************************_s*****************************)
Definition qd210_s := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qa220 (if_then_else_M (EQ_M (to x4) (i 3)) qd211 O) )))))).



Definition qd201_s :=

 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa202 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa202 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa202
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa301
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa301
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa301 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qd211 O)))))))).     



Definition qd120_s := 

(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qa220 (if_then_else_M (EQ_M (to x4) (i 3)) qd121 O) )))))).


Definition qd111_s :=
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qd211 (if_then_else_M (EQ_M (to x4) (i 2))  qd121  O))))))).

 

Definition qd021_s :=

 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa031
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa031
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa031
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qd121  O )))))))).


(***************_SS*************************)

Definition qd200_ss :=
 (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_s (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qd210_s (if_then_else_M (EQ_M (to x3) (i 3))  qd201_s O))))).


Definition qd110_ss :=
(if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qd210_s (if_then_else_M (EQ_M (to x3) (i 2))  qd120_s (if_then_else_M (EQ_M (to x3) (i 3))  qd111_s O)))))).





Definition qd101_ss := 
(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_s (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_s  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qd201_s
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qd111_s O)))))).



Definition qd020_ss := 

(if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_s (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qd120_s (if_then_else_M (EQ_M (to x3) (i 1)) qd021_s  O))))).


Definition qd011_ss :=

(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_s (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_s (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qd111_s (if_then_else_M (EQ_M (to x3) (i 2)) qd021_s  O)))))).

(********************************************************)

Definition qd100_sss := 
(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qd200_ss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qd110_ss (if_then_else_M (EQ_M (to x2) (i 3)) qd101_ss O)))))).



Definition qd010_sss := 

 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qd110_ss (if_then_else_M (EQ_M (to x2) (i 2))  qd020_ss (if_then_else_M (EQ_M (to x2) (i 3))  qd011_ss O)))))).


Definition qd001_sss := 
(if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_ss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qd101_ss (if_then_else_M (EQ_M (to x2) (i 2)) qd011_ss O)))))).


Definition t46 := 
msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qd100_sss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qd010_sss (if_then_else_M (EQ_M (to x1) (i 3)) qd001_sss   O) ) )))).



Definition phi45:= phi44 ++ [t46].



(*********************************phi46****************)
(*******alpha =2, beta =3********************)
 
Definition qd221 :=  (if_then_else_M (EQ_M (reveal  x6) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 




(if_then_else_M (EQ_M (reveal  x6) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21
(if_then_else_M (EQ_M (reveal  x6) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 

 (if_then_else_M (EQ_M (reveal  x6) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21


(if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5 

(********************i2************)
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4

(*****i1****)
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) mx2rn1 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1

 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 O)) ))))))))))))))))))))))))))).


Definition qd220_s :=
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa230
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa230
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qa230
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qa230

 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa320
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa320
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa320

(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3))  qd221 O)))))))))))))).






Definition qd121_s := 


 (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa122
    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa122
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa122
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa122
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa131
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa131
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa131
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa131
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa131
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa131
     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) qd221 O)))))))))))).

Definition qd210_ss := 

(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa310_s
 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa310_s
  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa310_s
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qd220_s (if_then_else_M (EQ_M (to x4) (i 3)) qa211_s O) )))))).


Definition qd120_ss := 

(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa130_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa130_s
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa130_s
   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qd220_s (if_then_else_M (EQ_M (to x4) (i 3)) qd121_s O) )))))).



Definition qd111_ss :=

(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112_s
  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112_s
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112_s
    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qa211_s
 (if_then_else_M (EQ_M (to x4) (i 2))  qd121_s  O))))))).

(*********************************************************************************)

Definition qd200_sss :=

(if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qa300_ss (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qd210_ss (if_then_else_M (EQ_M (to x3) (i 3))  qa201_ss O))))).


Definition qd110_sss :=
 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qd210_ss (if_then_else_M (EQ_M (to x3) (i 2))  qd120_ss (if_then_else_M (EQ_M (to x3) (i 3))  qd111_ss O)))))).




Definition qd101_sss := 

(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa102_ss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa102_ss  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qa201_ss
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qd111_ss O)))))).



Definition qd020_sss :=

(if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa030_ss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qd120_ss (if_then_else_M (EQ_M (to x3) (i 1)) qa021_ss  O))))).



Definition qd011_sss :=

(if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_ss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_ss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qd111_ss (if_then_else_M (EQ_M (to x3) (i 2)) qa021_ss  O)))))).


(*************************************************)
Definition qd100_ssss :=
(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qd200_sss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qd110_sss (if_then_else_M (EQ_M (to x2) (i 3)) qd101_sss O)))))).



Definition qd010_ssss := 
(if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qd110_sss (if_then_else_M (EQ_M (to x2) (i 2))  qd020_sss (if_then_else_M (EQ_M (to x2) (i 3))  qd011_sss O)))))).



Definition qd001_ssss :=
(if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qa002_sss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qd101_sss (if_then_else_M (EQ_M (to x2) (i 2)) qd011_sss O)))))).




Definition t47 :=
msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qd100_ssss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qd010_ssss (if_then_else_M (EQ_M (to x1) (i 3)) qd001_ssss   O) ) )))).



Definition phi46 := phi45 ++ [t47].


(*********************************************************************************)
(**********************phi47******************************************************)

(*******alpha=2, beta = 3*****************)
Definition qd321 :=   (if_then_else_M (EQ_M (reveal  x7) (i 3) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M (EQ_M (reveal  x7) (i 2) ) & (EQ_M (to  x3) (i 2)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 2)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) mx6rn6 (****)

(if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 2)) & (EQ_M (to x6) (i 2)) & (EQ_M (to x5) (i 2))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5
  O))))))))))))))))))))))).

(********alpha=1, beta =3**************)
Definition qd231 :=   (if_then_else_M (EQ_M (reveal  x7) (i 3) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M (EQ_M (reveal  x7) (i 1) ) &  (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 3))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x1) (i 3)) mx1rn1
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x2) (i 3)) mx2rn2
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x3) (i 3)) mx3rn3
 (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x4) (i 3)) mx4rn4
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x5) (i 3)) mx5rn5
  (if_then_else_M (EQ_M (reveal x7) (i 3)) & (EQ_M (to x6) (i 3)) mx6rn6

(if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) mx2rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) mx3rn1
  (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) mx3rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) mx4rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) mx4rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) mx4rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) mx5rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) mx5rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) mx5rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) mx5rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x1) new) mx6rn1
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x2) new) mx6rn2
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x3) new) mx6rn3
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x4) new) mx6rn4
 (if_then_else_M (EQ_M (reveal x7) (i 1)) & (EQ_M (to x6) (i 1)) & (EQ_M (to x5) (i 1))& (notb (EQ_M (act x6) new)) & (EQ_M (act x5) new) mx6rn5 
 O))))))))))))))))))))))).

(********************************************************************************************)


Definition qd221_s :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa222 
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa222 

(********************i2************)
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qd231
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qd231
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qd231
   (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qd231
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qd231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qd231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qd231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qd231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qd231
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qd231


(*****i1****)
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qd321
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qd321
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qd321
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qd321
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qd321

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qd321

(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qd321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qd321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qd321
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qd321
 O)) ))))))))))))))))))))))).

Definition qd320_s := (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330  
  (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 2)) & (EQ_M (to x5) (i 2)) & (EQ_M (to x4) (i 2))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qd321 O)))))))))))).

Definition qd230_s := (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x1) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa330
  (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa330
   (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x1) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x2) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x3) new) qa330
(if_then_else_M (EQ_M (reveal x6) (i 1)) & (EQ_M (to x5) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x5) new)) & (EQ_M (act x4) new) qa330
 (if_then_else_M (EQ_M (reveal x6) (i 3) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qd231 O)))))))))))).

Definition qd131_s :=   (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3)) qa132
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa132
  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3))  qa132
 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (to x6) (i 1)) qd231 O))))))).


Definition qd311_s :=  (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x1) (i 3))  qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x2) (i 3))  qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x3) (i 3)) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x4) (i 3)) qa312
 (if_then_else_M (EQ_M (reveal x6) (i 3)) & (EQ_M (to x5) (i 3)) qa312 (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (to x6) (i 2)) qd321 O))))))).
(***********************************************************************)
(***********************************************************************)



Definition qd220_ss :=
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qd230_s
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new)  qd230_s
  (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qd230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new)  qd230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new)  qd230_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new)  qd230_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qd320_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qd320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qd320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qd320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qd320_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x4) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qd320_s

(if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 3))  qd221_s O)))))))))))))).



Definition qd211_ss := (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3))  qa212_s
 (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa212_s
   (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa212_s
  (if_then_else_M (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa212_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qd311_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qd311_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qd311_s
  (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qd311_s
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qd311_s
(if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qd311_s
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qd221_s  O)))))))))))).


Definition qd202_ss :=    (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qa302_s
   (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 1)) & (EQ_M (to x4) (i 1)) & (EQ_M (to x3) (i 1))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qa302_s
 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa212_s O) ))))))).

Definition qd121_ss  :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa122_s
    (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa122_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa122_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa122_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qd131_s
      (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qd131_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qd131_s
   (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x1) new) qd131_s
(if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x2) new) qd131_s
 (if_then_else_M (EQ_M (reveal x5) (i 2)) & (EQ_M (to x4) (i 2)) & (EQ_M (to x3) (i 2))& (notb (EQ_M (act x4) new)) & (EQ_M (act x3) new) qd131_s
     (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (to x5) (i 1)) qd221_s O)))))))))))).



Definition qd031_ss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa032_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa032_s
  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qd131_s O)))))).

Definition qd130_ss :=(if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 1)) qd230_s (if_then_else_M (EQ_M (to x5) (i 3)) qd131_s  O)))).

Definition qd301_ss :=  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x1) (i 3)) qa302_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x2) (i 3)) qa302_s
   (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 3)) qa302_s
  (if_then_else_M  (EQ_M (reveal x5) (i 3)) & (EQ_M (to x4) (i 3)) qa302_s
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qd311_s O)))))).
Definition qd310_ss := 
  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O (if_then_else_M (EQ_M (reveal x5) (i 3) ) O   (if_then_else_M (EQ_M (to x5) (i 2)) qd320_s (if_then_else_M (EQ_M (to x5) (i 3)) qd311_s  O)))).

(*************************************************************************************************)
(*************************************************************************************************)

Definition qd210_sss := 
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qd310_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qd310_ss
  (if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qd310_ss
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O
 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2)) qd220_ss (if_then_else_M (EQ_M (to x4) (i 3)) qd211_ss O) )))))).

Definition qd201_sss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qd202_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qd202_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qd202_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qd301_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qd301_ss
(if_then_else_M  (EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1)) & (EQ_M (to x2) (i 1))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qd301_ss 
 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qd211_ss O))))))))     .


Definition qd120_sss :=   (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qd130_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qd130_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new) qd130_ss
   (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M (EQ_M (to x4) (i 1)) qd220_ss (if_then_else_M (EQ_M (to x4) (i 3)) qd121_ss O) )))))).

Definition qd111_sss := (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))  qa112_ss
  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))  qa112_ss
 (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3))  qa112_ss
    (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (to x4) (i 1))  qd211_ss
 (if_then_else_M (EQ_M (to x4) (i 2))  qd121_ss  O))))))).


Definition qd102_sss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (to x4) (i 1)) qd202_ss (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qa112_ss O )))).

Definition qd021_sss :=  (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3)) qa022_ss 
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3)) qa022_ss
(if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 3)) qa022_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qd031_ss
 (if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x1) new) qd031_ss
(if_then_else_M  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) & (EQ_M (to x2) (i 2))& (notb (EQ_M (act x3) new)) & (EQ_M (act x2) new)  qd031_ss
  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qd121_ss  O )))))))).


Definition qd300_sss := (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) qd310_ss (if_then_else_M (EQ_M (to x4) (i 3)) qd301_ss O)))) .

Definition qd030_sss := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) qd130_ss (if_then_else_M (EQ_M (to x4) (i 3)) qd031_ss O)))) .
(********************************************************************************************)
(*******************************************************************************************)
 
Definition qd200_ssss := (if_then_else_M  (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) & (EQ_M (to x1) (i 1))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new)  qd300_sss (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new)  qd210_sss (if_then_else_M (EQ_M (to x3) (i 3))  qd201_sss O))))).

Definition qd110_ssss := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O   (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  qd210_sss (if_then_else_M (EQ_M (to x3) (i 2))  qd120_sss (if_then_else_M (EQ_M (to x3) (i 3))  qd111_sss O)))))).


Definition qd101_ssss :=  (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qd102_sss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qd102_sss  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (to x3) (i 1)) qd201_sss
(if_then_else_M (EQ_M (to x3 ) (i 2)) & (EQ_M (act x3) new) qd111_sss O)))))).


Definition qd020_ssss := (if_then_else_M  (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2)) & (EQ_M (to x1) (i 2))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new) qd030_sss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O 
 (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qd120_sss (if_then_else_M (EQ_M (to x3) (i 1)) qd021_sss  O))))).

Definition qd011_ssss := (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x1) (i 3)) qa012_sss (if_then_else_M (EQ_M (reveal x3) (i 3)) & (EQ_M (to x2) (i 3)) qa012_sss (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qd111_sss (if_then_else_M (EQ_M (to x3) (i 2)) qd021_sss  O)))))).


 

Definition qd002_ssss :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) qd102_sss (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) qa012_sss O)))).



(***********************************************************************)


Definition qd100_sssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qd200_ssss  (if_then_else_M (EQ_M (to x2 ) (i 2)) & (EQ_M (act x2) new) qd110_ssss (if_then_else_M (EQ_M (to x2) (i 3)) qd101_ssss O)))))).


Definition qd010_sssss :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O    (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new)  qa110 (if_then_else_M (EQ_M (to x2) (i 2))  qd020_ssss (if_then_else_M (EQ_M (to x2) (i 3))  qd011_ssss O)))))).

Definition qd001_sssss := (if_then_else_M (EQ_M (reveal x2) (i 3)) & (EQ_M (to x1) (i 3)) qd002_ssss  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (to x2) (i 1)) qd101_ssss (if_then_else_M (EQ_M (to x2) (i 2)) qd011_ssss O)))))).


Definition t48 := msg (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qd100_sssss (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) qd010_sssss (if_then_else_M (EQ_M (to x1) (i 3)) qd001_sssss   O) ) )))).
Definition phi47:= phi46 ++ [t48].
(*********************************)

Definition phi48 := phi47 ++ [t19].  
Definition mphi47 := (conv_mylist_listm phi47). 
Definition mphi48 := (conv_mylist_listm phi48).

Check hd.
Definition m1:= hd new mphi47.  
Eval compute in check_eq_msg (nth 2 mphi47 O)  (nth 2 mphi48 O).
Eval compute in check_eq_msg (nth 3 mphi47 O)  (nth 3 mphi48 O).

 
Eval compute in  (nth 4 mphi47 O).   
Eval compute in (size_msg 0 (nth 4 mphi47 O)). 
Eval compute in (nth 4 mphi48 O).
Eval compute in check_eq_msg (nth 4 mphi47 O)  (nth 4 mphi48 O).
Eval compute in check_eq_msg (nth 5 mphi47 O)  (nth 5 mphi48 O).
Eval compute in check_eq_msg (nth 6 mphi47 O)  (nth 6 mphi48 O).
Eval compute in (check_eq_listm (check_eq_msg) mphi47 mphi48) .
