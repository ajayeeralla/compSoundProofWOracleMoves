Load "extra_theorems".

(*****************Real or random Secrecy*****************************************)
(********************************************************************************)
(******protocol Pi1 :The oracle reveals the actual Key if there is any*************)

(********************************************************************************)


Definition phi (n:nat) := mylist (n+2).
Eval compute in (phi 0).
Definition phi0  := [ msg (G 0) ; msg (g 0)].
Definition mphi0 := (conv_mylist_listm phi0).
Definition grn (n:nat) := (exp (G 0) (g 0) (r n)).

Definition x1 := (f mphi0).

(******start state****************)

Definition qa00000000:= (if_then_else_M (EQ_M (reveal x1) (i 1) ) O (if_then_else_M (EQ_M (reveal x1) (i 2) ) O  (if_then_else_M (EQ_M (reveal x1) (i 3) ) O (if_then_else_M (EQ_M (reveal x1) (i 4) ) O (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) (grn 1)  (if_then_else_M (EQ_M (to x1) (i 1)) (grn 1)  (if_then_else_M ((EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)) (grn 2)  (if_then_else_M (EQ_M (to x1) (i 2)) (grn 2) (if_then_else_M ((EQ_M (to x1) (i 3)) & (EQ_M (act x1) new)) (grn 3)  (if_then_else_M (EQ_M (to x1) (i 3)) (grn 3) (if_then_else_M ((EQ_M (to x1) (i 4)) & (EQ_M (act x1) new)) (grn 4)  (if_then_else_M (EQ_M (to x1) (i 4)) (grn 4) O)) ))) ) )))))).

(************************)

Definition t12:= msg qa00000000.
Definition phi1 := phi0 ++ [ t12 ].


(****************************@@@@phi2@@@@@@@@@@@@*******************************)
(*******************************************************************************)
Definition tta1 (x y:message) (j :nat) := (EQ_M (reveal x) (i j)) & (EQ_M (to y) (i j)).
Definition tta2 (x x1 x2 :message) (j:nat) := (EQ_M (reveal x) (i j)) & (EQ_M (to x2) (i j)) & (EQ_M (to x1) (i j))& (notb (EQ_M (act x2) new)) & (EQ_M (act x1) new).
Definition mphi1 := (conv_mylist_listm phi1).
Definition mx1rn1 := (exp (G 0) (m x1) (r 1)).
Definition mx1rn2 := (exp (G 0) (m x1) (r 2)).

Definition x2 := (f mphi1).


(**********qa00000000 -> qa10000000,  qa00001000, qa01000000,qa00000100,  qa00100000,  qa00000010, qa00010000 ,qa00000001  *************************************************)

Definition qa10000000 :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M (EQ_M (to x2) (i 1)) acc  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 5)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 5) (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 6)  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 6) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 7)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 7) O))))))))))).

Definition qa00001000 :=  (if_then_else_M (tta1 x2 x1 1) mx1rn2 (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 8)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 8) (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 9)  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 9) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 10)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 10) O)))))))))).


Definition qa01000000 :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O  (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 11)   (if_then_else_M (EQ_M (to x2) (i 1)) (grn 11)  (if_then_else_M (EQ_M (to x2) (i 2)) acc  (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 12)  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 12) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 13)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 13) O))))))))))).

 Definition qa00000100 :=  (if_then_else_M (EQ_M (reveal x2) (i 2) ) & (EQ_M (to x1) (i 2)) mx1rn2 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O  (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 14)  (if_then_else_M (EQ_M (to x2) (i 1)) (grn 14) (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 15)  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 15) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 16)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 16) O)))))))))).

 Definition qa00100000 :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O   (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 16)  (if_then_else_M (EQ_M (to x2) (i 1)) (grn 16) (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 17)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 17) (if_then_else_M (EQ_M (to x2) (i 3)) acc (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 18)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 18) O))))))))))).

Definition  qa00000010  :=   (if_then_else_M (EQ_M (reveal x2) (i 3) ) & (EQ_M (to x1) (i 3)) mx1rn2 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 15)  (if_then_else_M (EQ_M (to x2) (i 1)) (grn 15)   (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 16)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 16) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 17)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 17) O)))))))))).

Definition  qa00010000  :=    (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O    (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 18)  (if_then_else_M (EQ_M (to x2) (i 1)) (grn 18)  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 19)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 19)  (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 20 )  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 20) (if_then_else_M (EQ_M (to x2) (i 4)) acc O))))))))))).
Definition  qa00000001 := (if_then_else_M (EQ_M (reveal x2) (i 4) ) & (EQ_M (to x1) (i 4)) mx1rn2 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 21)  (if_then_else_M (EQ_M (to x2) (i 1)) (grn 21)  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 22)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 22)  (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 23 )  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 23) O )))))))))).



Definition t13 := msg  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa10000000  (if_then_else_M (EQ_M (to x2) (i 1)) qa00001000  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) qa01000000  (if_then_else_M (EQ_M (to x2) (i 2)) qa00000100 (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa00100000  (if_then_else_M (EQ_M (to x2) (i 3))  qa00000010 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa00010000  (if_then_else_M (EQ_M (to x2) (i 4))  qa00000001 O)) ))) ) )))))).
Definition phi2:= phi1 ++ [t13].

(****************************@@@@phi3@@@@@@@@@@@@*******************************)
(*******************************************************************************)



Definition mphi2 := (conv_mylist_listm phi2).
Definition mx2rn1 := (exp (G 0) (m x2) (r 1)).
Definition mx2rn2 := (exp (G 0) (m x2) (r 2)).
Definition grn3:= (exp (G 0) (g 0) (r 3)).
Definition x3 := (f mphi2).

(***************add oracle moves next from here******************************)

(********** qa00000000 -> qa10000000 -> *******)


Definition qa20000000:=  (if_then_else_M (tta2 x3 x2 x1 1) mx2rn1    (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 24)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 24)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 25)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 25) (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 26)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 26) O))))))).
Definition qa11000000 :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O  (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M (EQ_M (to x3) (i 1))  acc  (if_then_else_M (EQ_M (to x3) (i 2))  acc  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 27)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 27)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 28)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 28) O)))))))))).
Definition qa10000100:= (if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn2 (if_then_else_M (EQ_M (to x3) (i 1))  acc  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 28)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 28)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 29)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 29) O))))))).

Definition qa10100000:= (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  acc    (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 30)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 30) (if_then_else_M (EQ_M (to x3) (i 3))  acc  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 31)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 31) O)))))))))).

Definition qa10000010 := (if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x1 3) mx2rn2 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M (EQ_M (to x3) (i 1))  acc    (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 32)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 32)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 33)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 33) O)))))))))).

Definition qa10010000:= (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M (EQ_M (to x3) (i 1))  acc    (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 34)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 34)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 35)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 35) (if_then_else_M (EQ_M (to x3) (i 4))  acc O)))))))))).

Definition qa10000001:= (if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x1 4) mx2rn2(if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (to x3) (i 1))  acc    (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 36)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 36)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 37)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 37) O)))))))))).

(***********qa00000000 -> qa00001000 -> *******)



Definition qa01001000 := (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O (if_then_else_M (EQ_M (to x3) (i 2))  acc  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 38)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 38)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 39)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 39) O)))))))))).

Definition qa00001100:= (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1(if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 40)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 40)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 41)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 41) O)))))))))).

Definition qa00101000:= (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1(if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 41)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 41) (if_then_else_M (EQ_M (to x3) (i 3))  acc   (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 42)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 42) O)))))))))).


Definition qa00001010 := (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1(if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x2 3) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O      (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 43)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 43)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 44)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 44) O)))))))))).

Definition qa00011000:=  (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O         (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 45)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 45)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 46)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 46) (if_then_else_M (EQ_M (to x3) (i 4))  acc O))))) ))))).

Definition qa00001001:= (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1(if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 47)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 47)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 48)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 48) O)))))))))).
Definition qa00002000 := 
(if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 8)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 8) (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 9)  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 9) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 10)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 10) O))))))))).

(*********qa00000000 ->qa01000000-> **********)


Definition qa02000000 := (if_then_else_M (tta2 x3 x1 x2 2) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 49)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 49)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 49)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 49)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 50)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 50) O)))))))))).


Definition qa01100000 :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O    (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 51)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 51) (if_then_else_M (EQ_M (to x3) (i 2))  acc  (if_then_else_M (EQ_M (to x3) (i 3))  acc (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 52)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 52) O)))))))))).

Definition qa01000010:=  (if_then_else_M (tta1 x3 x1 3) mx1rn1  (if_then_else_M (tta1 x3 x2 3) mx2rn2  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 53)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 53) (if_then_else_M (EQ_M (to x3) (i 2))  acc    (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 54)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 54) O)))))))))).

Definition qa01010000:=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 55)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 55)  (if_then_else_M (EQ_M (to x3) (i 2))  acc  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 56)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 56)  (if_then_else_M (EQ_M (to x3) (i 4))  acc O)))))) )))).

Definition qa01000001:=  (if_then_else_M (tta1 x3 x1 4) mx1rn1  (if_then_else_M (tta1 x3 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 57)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 57) (if_then_else_M (EQ_M (to x3) (i 2))  acc   (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 58)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 58) O)))))))))).
(**********qa00000000 ->qa00000100->****)


Definition qa00000110 := (if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1(if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x2 3) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O    (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 59)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 59)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 60)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 60) O)))))))))).

Definition qa00010100:= (if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1(if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O    (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 61)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 61)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 62)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 62) (if_then_else_M (EQ_M (to x3) (i 4))  acc O)))))))))).

Definition qa00000101:= (if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1(if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 63)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 63)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 64)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 64) O)))))))))).
Definition qa00000200 := (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O  (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 14)  (if_then_else_M (EQ_M (to x2) (i 1)) (grn 14) (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 15)  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 15) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 16)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 16) O))))))))).
(***************qa00000000 ->qa001000000-> *)



Definition qa00200000:=  (if_then_else_M (tta2 x3 x1 x2 3) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O (if_then_else_M (EQ_M (to x3) (i 3))  acc  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 65)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 65) (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 66)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 66)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 67)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 67) O))))))))))).



Definition qa00100100 := (if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O (if_then_else_M (EQ_M (to x3) (i 3))  acc   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 70)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 70)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 71)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 71) O)))))))))).

Definition qa00110000:= (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 72)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 72)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 73)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 73) (if_then_else_M (EQ_M (to x3) (i 3))  acc  (if_then_else_M (EQ_M (to x3) (i 4))  acc  O)))))))))).

Definition qa00100001:=  (if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x2 4) mx2rn1  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 74)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 74)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 75)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 75) (if_then_else_M (EQ_M (to x3) (i 3))  acc O)))))))))).

(*******qa00000000 ->  qa00000010->********)

(********resume here******************)


Definition qa00010010:= (if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x2 3) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O    (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 76)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 76)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 77)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 77) (if_then_else_M (EQ_M (to x3) (i 4))  acc O)))))))))).

Definition qa00000011:= (if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x2 3) mx2rn1(if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 78)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 78)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 79)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 79) O)))))))))).
Definition  qa00000020 := (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 15)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 15)   (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 16)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 16) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 17)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 17) O))))))))).

(****qa00000000 ->  qa00010000 -> *)


Definition qa00020000 := (if_then_else_M (tta2 x3 x1 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 80)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 80)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 81)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 81)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 82)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 82) O)))))))))).


(*Definition qa01010000 := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M (EQ_M (to x3) (i 2))  acc (if_then_else_M (EQ_M (to x3) (i 4))  acc  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 83)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 83)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 84)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 84) O)))))))))).
*)


(********* qa00000000 ->  qa00000001 ->*********)
Definition qa00000002 :=   (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 21)  (if_then_else_M (EQ_M (to x2) (i 1)) (grn 21)  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 22)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 22)  (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 23 )  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 23) O ))))))))).



(*****************************************************************************)
(*****************************************************************************)



Definition qa10000000_s :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M (EQ_M (to x2) (i 1))  qa20000000  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new))  qa11000000  (if_then_else_M (EQ_M (to x2) (i 2))  qa10000100(if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new))  qa10100000  (if_then_else_M (EQ_M (to x2) (i 3))  qa10000010 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new))  qa10010000  (if_then_else_M (EQ_M (to x2) (i 4))  qa10000001 O))))))))))).

Definition qa00001000_s :=  (if_then_else_M (tta1 x2 x1 1) qa00002000 (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) qa01001000  (if_then_else_M (EQ_M (to x2) (i 2)) qa00001100 (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa00101000 (if_then_else_M (EQ_M (to x2) (i 3)) qa00001010 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa00011000  (if_then_else_M (EQ_M (to x2) (i 4)) qa00001001 O)))))))))).


Definition qa01000000_s :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O  (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa11000000  (if_then_else_M (EQ_M (to x2) (i 2)) qa02000000 (if_then_else_M (EQ_M (to x2) (i 1)) qa01001000  (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa01100000  (if_then_else_M (EQ_M (to x2) (i 3)) qa01000010 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa01010000  (if_then_else_M (EQ_M (to x2) (i 4)) qa01000001 O))))))))))).

 Definition qa00000100_s :=  (if_then_else_M (EQ_M (reveal x2) (i 2) ) & (EQ_M (to x1) (i 2)) qa00000200 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O  (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa10000100  (if_then_else_M (EQ_M (to x2) (i 1)) qa00001100 (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa00100100  (if_then_else_M (EQ_M (to x2) (i 3)) qa00000110 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa00010100  (if_then_else_M (EQ_M (to x2) (i 4)) qa00000101 O)))))))))).

 Definition qa00100000_s :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O   (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa10100000  (if_then_else_M (EQ_M (to x2) (i 1)) qa00101000  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) qa01100000 (if_then_else_M (EQ_M (to x2) (i 2)) qa00100100(if_then_else_M (EQ_M (to x2) (i 3)) qa00200000 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa00110000  (if_then_else_M (EQ_M (to x2) (i 4)) qa00100001 O))))))))))).

Definition  qa00000010_s  :=   (if_then_else_M (EQ_M (reveal x2) (i 3) ) & (EQ_M (to x1) (i 3))  qa00000020 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new))  qa10000010 (if_then_else_M (EQ_M (to x2) (i 4))  qa00001010   (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new))  qa01000010  (if_then_else_M (EQ_M (to x2) (i 2))  qa00000110 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new))  qa00010010  (if_then_else_M (EQ_M (to x2) (i 4))  qa00000011 O)))))))))).

Definition  qa00010000_s  :=    (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O    (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa10010000  (if_then_else_M (EQ_M (to x2) (i 1)) qa00011000  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) qa01010000 (if_then_else_M (EQ_M (to x2) (i 2)) qa00010100  (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa00110000  (if_then_else_M (EQ_M (to x2) (i 3)) qa00010010 (if_then_else_M (EQ_M (to x2) (i 4)) qa00020000 O))))))))))).
Definition  qa00000001_s := (if_then_else_M (EQ_M (reveal x2) (i 4) ) & (EQ_M (to x1) (i 4))  qa00000002  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new))  qa10000001  (if_then_else_M (EQ_M (to x2) (i 1))  qa00001001  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new))  qa01000001  (if_then_else_M (EQ_M (to x2) (i 2))  qa00000101 (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new))  qa00100001 (if_then_else_M (EQ_M (to x2) (i 3))  qa00000011  O)))))))))).



Definition t14 := msg  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa10000000_s  (if_then_else_M (EQ_M (to x2) (i 1)) qa00001000_s  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) qa01000000_s  (if_then_else_M (EQ_M (to x2) (i 2)) qa00000100_s (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa00100000_s  (if_then_else_M (EQ_M (to x2) (i 3))  qa00000010_s (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa00010000_s  (if_then_else_M (EQ_M (to x2) (i 4))  qa00000001_s O)) ))) ) )))))).
Definition phi3:= phi2 ++ [t14].


(****************************@@@@phi4@@@@@@@@@@@@*******************************)
(*******************************************************************************)
Definition mphi3 := (conv_mylist_listm phi3).

Definition x4 := (f mphi3).

(*****************///start qa10000000///*******************************************)
(***********************************************************************************)

 (*************qa00000000 -> qa10000000 -> qa20000000 -> *)
Definition qa30000000 := (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O   (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 85) (if_then_else_M (EQ_M (to x4) (i 2)) (grn 85) (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 85) (if_then_else_M (EQ_M (to x4) (i 3)) (grn 85)   (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 86)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 86) O))))))))).
Definition qa21000000:=  (if_then_else_M (tta2 x4 x1 x2 1) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 2))  acc   (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 85) (if_then_else_M (EQ_M (to x4) (i 3)) (grn 85)   (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 86)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 86) O))))))))).

Definition qa20000100 := (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2  (if_then_else_M (tta2 x4 x1 x2 1) mx2rn1  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 87) (if_then_else_M (EQ_M (to x4) (i 3)) (grn 87)   (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 88)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 88) O))))))))).


Definition qa20100000:= (if_then_else_M (tta2 x4 x1 x2 1) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O 
 (if_then_else_M (EQ_M (to x4) (i 3))  acc
(if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 89)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 89)  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 90)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 90) O))))))))).

Definition qa20000010:=  (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2 (if_then_else_M (tta2 x4 x1 x2 1) mx2rn1  (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 91)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 91)  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 92)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 92) O))))))).
Definition qa20010000 := (if_then_else_M (tta2 x4 x1 x2 1) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O   (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 93) (if_then_else_M (EQ_M (to x4) (i 2)) (grn 93)   (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 94)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 94) (if_then_else_M (EQ_M (to x4) (i 4))  acc  O))))))))).

Definition qa20000001:=  (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (tta2 x4 x1 x2 1) mx2rn1  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 95)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 95)  (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 96)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 96) O))))))))).

(*******************************qa00000000 -> qa10000000 ->qa11000000 ->*******************)

Definition qa12000000 := (if_then_else_M (tta2 x4 x1 x2 2) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc  (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 97) (if_then_else_M (EQ_M (to x4) (i 3)) (grn 97)   (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 98)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 98) O))))))))).


Definition  qa11100000 := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc (if_then_else_M (EQ_M (to x4) (i 2))  acc  (if_then_else_M (EQ_M (to x4) (i 3))  acc  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 99)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 99) O))))))))).

Definition  qa11000010:= (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc (if_then_else_M (EQ_M (to x4) (i 2))  acc  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 100)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 100) O))))))))).
Definition qa11010000 := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O   (if_then_else_M (EQ_M (to x4) (i 1))  acc (if_then_else_M (EQ_M (to x4) (i 2))  acc   (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 101)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 101) (if_then_else_M (EQ_M (to x4) (i 4))  acc O))))))))).



(************************qa00000000 -> qa10000000 -> qa10000100 ->***************************)

(*******************qa20000100, qa10100100, qa10000110, qa10010100, qa10000101*****************************)

Definition qa10100100 := (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc  (if_then_else_M (EQ_M (to x4) (i 3))  acc     (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 102)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 102) O))))))))).


Definition qa10000110 :=  (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O   (if_then_else_M (EQ_M (to x4) (i 1))  acc      (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 103)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 103) O))))))))).

Definition  qa10010100 :=  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O   (if_then_else_M (EQ_M (to x4) (i 1))  acc     (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 104)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 104) (if_then_else_M (EQ_M (to x4) (i 4))  acc  O))))))))).
Definition qa10000101 := (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2 (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc     (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 105)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 105) O))))))))).

(***************************qa00000000 -> qa10000000 ->qa10100000->************************************************)
(*qa20100000, qa10200000, qa11100000, qa10100100, qa10110000, qa10100001*********)


Definition qa10200000 :=  (if_then_else_M (tta2 x4 x1 x2 3) mx2rn1  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc  (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 106)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 106) (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 107)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 107) O))))))))).

Definition  qa10110000 :=  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc   (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 108)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 108) (if_then_else_M (EQ_M (to x4) (i 3))  acc  (if_then_else_M (EQ_M (to x4) (i 4))  acc  O))))))))).

Definition  qa10100001 :=  (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc   (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 109)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 109) (if_then_else_M (EQ_M (to x4) (i 3))  acc  O))))))))).


(*****************************************qa00000000 -> qa10000000 ->qa10000010 -> ******************************************************************)
(****qa20000010, qa11000010, qa10000110, qa10010010,qa10000011****)

Definition  qa10010010 := (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc    (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 111)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 111) (if_then_else_M (EQ_M (to x4) (i 4))  acc O))))))))).

Definition qa10000011 :=  (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2  (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (to x4) (i 1))  acc (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 112)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 112) O))))))))).

(**************qa00000000 -> qa10000000 -> qa10010000 ->****************)
(****qa20010000,qa10020000, qa11010000, qa10010100, qa10110000,qa10010010****)


Definition qa10020000 :=  (if_then_else_M (tta2 x4 x1 x2 4) mx2rn1  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 1))  acc  (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 113)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 113) (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 114)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 114) O))))))))).




(************************qa00000000 -> qa10000000 -> qa10000001 -> ******************************)
(****** qa20000001,  qa11000001  qa10000101 qa10100001 qa10000011 **)

Definition   qa11000001 :=  (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (to x4) (i 1))  acc  (if_then_else_M (EQ_M (to x4) (i 2))  acc (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 115)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 115) O))))))))).



(*************************qa00000000 -> qa00001000 -> qa01001000 ->******************************)
(*qa02001000 qa01101000 qa01001010 qa01011000 qa01001001 *)


Definition qa02001000 := (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2 (if_then_else_M (tta2 x4 x1 x2 2) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O  (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 116)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 116)  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 117)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 117) O))))))))).

Definition  qa01101000 := (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 2))  acc  (if_then_else_M (EQ_M (to x4) (i 3))  acc  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 118)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 118) O))))))))). 
Definition  qa01001010 :=  (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2  (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 2))  acc  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 119)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 119) O))))))))). 
Definition  qa01011000 := (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M (EQ_M (to x4) (i 2))  acc  (if_then_else_M (EQ_M (to x4) (i 4))  acc  (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 120)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 120) O))))))))). 
Definition  qa01001001 :=  (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2  (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O  (if_then_else_M (EQ_M (to x4) (i 2))  acc    (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 121)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 121) O))))))))).

(*********** qa00000000 -> qa00001000 ->qa00001100 -> ****)
(*qa00101100 qa00001110 qa00011100 qa00001101 *************)


Definition qa00101100:=  (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O  (if_then_else_M (EQ_M (to x4) (i 3))  acc    (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 122)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 122) O))))))))).

Definition   qa00001110 :=  (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2  (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2  (if_then_else_M (EQ_M (reveal x4) (i 4) ) O  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 122)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 122) O))))))))).
Definition  qa00011100 :=  (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O    (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 123)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 123) (if_then_else_M (EQ_M (to x4) (i 4))  acc  O))))))))).

Definition  qa00001101 := (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2  (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 124)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 124) O))))))))).

(**** qa00000000 -> qa00001000 -> qa00101000 -> **************************)

(***qa00201000 qa01101000 qa00101100 qa00111000 qa00101001****)

Definition qa00201000 := (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2 (if_then_else_M (tta2 x4 x1 x2 3) mx2rn1  (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 125)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 125)  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 126)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 126) O))))))))).

Definition  qa00111000 := (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O    (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 127)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 127) (if_then_else_M (EQ_M (to x4) (i 3))  acc  (if_then_else_M (EQ_M (to x4) (i 4))  acc O))))))))).
Definition  qa00101001 := (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2 (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2   (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 128)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 128)  (if_then_else_M (EQ_M (to x4) (i 3))  acc O))))))))).

(***** qa00000000 -> qa00001000 -> qa00001010 ->********************************)
(*** qa01001010  qa00001110  qa00011010  qa00001011 *)

Definition  qa00011010 :=  (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2  (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O     (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 129)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 129) (if_then_else_M (EQ_M (to x4) (i 4))  acc O))))))))).
Definition  qa00001011  :=  (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2  (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2  (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 128)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 128) O))))))))).


(*********qa00000000 -> qa00001000 ->qa00011000 ->******************************)
(***qa00021000 qa01011000 qa00011100 qa00111000 qa00011010 *)

Definition qa00021000 :=  (if_then_else_M (tta1 x4 x1 1) mx1rn1 (if_then_else_M (tta1 x4 x2 1) mx2rn2 (if_then_else_M (tta2 x4 x1 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 129)  (if_then_else_M (EQ_M (to x4) (i 2)) (grn 129)  (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 130)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 130) O))))))))).

(***********qa00000000 -> qa00001000 ->qa00001001->********************************)

(********qa01001001 qa00001101 qa00101001 qa00001011***)

(****************************qa00000000 -> qa01000000 -> qa02000000 ->*****************)
(**qa12000000, qa02001000, qa02100000, qa02000010, qa02010000, qa02000001************)

Definition  qa02100000 := (if_then_else_M (tta2 x4 x1 x2 2) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O   (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 131)  (if_then_else_M (EQ_M (to x4) (i 1)) (grn 131) (if_then_else_M (EQ_M (to x4) (i 3)) acc (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 132)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 132) O))))))))).

Definition  qa02000010 :=  (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2  (if_then_else_M (tta2 x4 x1 x2 2) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 134)  (if_then_else_M (EQ_M (to x4) (i 1)) (grn 134)  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 135)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 135) O))))))))).
Definition  qa02010000 := (if_then_else_M (tta2 x4 x1 x2 2) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O   (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 136)  (if_then_else_M (EQ_M (to x4) (i 1)) (grn 136) (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 137)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 137) (if_then_else_M (EQ_M (to x4) (i 4)) acc O))))))))).
Definition  qa02000001 :=  (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (tta2 x4 x1 x2 2) mx2rn1  (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 138)  (if_then_else_M (EQ_M (to x4) (i 1)) (grn 138)  (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 139)  (if_then_else_M (EQ_M (to x4) (i 3)) (grn 139) O))))))).

(***************qa00000000 -> qa01000000 -> qa01100000 ->***********************)
(**qa02100000, qa01200000, qa11100000, qa01101000, qa01110000, qa01100001************)


Definition  qa01200000 := (if_then_else_M (tta2 x4 x1 x2 3) mx2rn1  (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 140)  (if_then_else_M (EQ_M (to x4) (i 1)) (grn 140) (if_then_else_M (EQ_M (to x4) (i 2)) acc  (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 141)  (if_then_else_M (EQ_M (to x4) (i 4)) (grn 141) O)))))).

Definition  qa01110000 := (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O   (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 142)  (if_then_else_M (EQ_M (to x4) (i 1)) (grn 142) (if_then_else_M (EQ_M (to x4) (i 2)) acc (if_then_else_M (EQ_M (to x4) (i 3)) acc (if_then_else_M (EQ_M (to x4) (i 4)) acc  O))))))))).


Definition  qa01100001 := (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O   (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 143)  (if_then_else_M (EQ_M (to x4) (i 1)) (grn 143) (if_then_else_M (EQ_M (to x4) (i 2)) acc (if_then_else_M (EQ_M (to x4) (i 3)) acc  O))))))))).
 
(****************************qa00000000 -> qa01000000 ->qa01000010 ->**************************************)

(* qa02000010, qa11000010 qa01001010 qa01010010 qa01000011 ******)

Definition  qa01010010 := (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 4) ) O   (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 144) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 144)  (if_then_else_M (EQ_M (to x4) (i 2)) acc (if_then_else_M (EQ_M (to x4) (i 4)) acc  O))))))))).
Definition  qa01000011 := (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2 (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 145) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 145) (if_then_else_M (EQ_M (to x4) (i 2)) acc  O))))))))).

(************************qa00000000 -> qa01000000 -> qa01000001 ->*******************)
(*  qa02000001,  qa11000001,  qa01001001 ,  qa01100001,  qa01000011**************)

(*****************///end qa01000000///**********************************************)
(***********************************************************************************)


(*****************///start qa00000100///**********************************************)
(***********************************************************************************)


 (*****************************qa00000000 -> qa00000100 -> qa00000110 ->********************************)
(* qa10000110, qa00001110 , qa00010110, qa00000111*)

Definition  qa00010110 := (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2 (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O  (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 146) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 146)  (if_then_else_M (EQ_M (to x4) (i 4)) acc  O))))))))).
Definition qa00000111 :=  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2 (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2 (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O  (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 147) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 147)  O))))))))).
(************qa00000000 -> qa00000100 ->qa00010100 ->**************************)
(*qa00020100, qa10010100 , qa00011100 , qa00110100, qa00010110***)


Definition qa00020100 :=  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2   (if_then_else_M (tta2 x4 x1 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 148) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 148)  (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 149) (if_then_else_M (EQ_M (to x4) (i 3)) (grn 149)  O))))))))).


Definition  qa00110100 :=  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O  (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 150) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 150)  (if_then_else_M (EQ_M (to x4) (i 3)) acc  (if_then_else_M (EQ_M (to x4) (i 4)) acc O))))))))).



(**********************qa00000000 -> qa00000100 -> qa00000101 ->**************************************************************)
(* qa10000101,  qa00001101 ,  qa00100101   qa00000111 *)

Definition   qa00100101 :=  (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2   (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O       (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 151) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 151) (if_then_else_M (EQ_M (to x4) (i 3)) acc O))))))))).


(*****************///end qa00000100///**********************************************)
(***********************************************************************************)


(*****************///start  qa001000000 ///**********************************************)
(***********************************************************************************)
(************qa00000000 -> qa001000000 -> qa00200000 ->*)
(*qa10200000, qa00201000 , qa01200000, qa00200100,qa00210000, qa00200001*)


Definition  qa00200100 :=   (if_then_else_M (tta1 x4 x1 2) mx1rn1 (if_then_else_M (tta1 x4 x2 2) mx2rn2  (if_then_else_M (tta2 x4 x1 x2 3) mx2rn1  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 4) ) O    (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 152) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 152) (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 153) (if_then_else_M (EQ_M (to x4) (i 4)) (grn 153) O))))))))).

Definition qa00210000 :=    (if_then_else_M (tta2 x4 x1 x2 3) mx2rn1  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 4) ) O      (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 153) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 153)  (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 154) (if_then_else_M (EQ_M (to x4) (i 2)) (grn 154)   (if_then_else_M (EQ_M (to x4) (i 4)) acc O))))))))).
Definition  qa00200001 :=  (if_then_else_M (tta1 x4 x1 4) mx1rn1 (if_then_else_M (tta1 x4 x2 4) mx2rn2 (if_then_else_M (tta2 x4 x1 x2 3) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O    (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 155) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 155)  (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 156) (if_then_else_M (EQ_M (to x4) (i 2)) (grn 156) O))))))))).


(************qa00000000 -> qa00100000 -> qa00100100 ->***********************)
(* qa00200100, qa10100100, qa00101100, qa00110100 qa00100101 *)

(************qa00000000 -> qa001000000 -> qa00110000 ->*********************)
(*qa00210000 qa00120000 qa10110000 qa00111000 qa01110000 qa00110100*)
(*
Definition qa00210000 :=  (if_then_else_M (EQ_M (to x4) (i 3)) acc   (if_then_else_M ((EQ_M (to x4) (i 4)) & (EQ_M (act x4) new)) (grn 157) (if_then_else_M (EQ_M (to x4) (i 4)) (grn 157) O))).
*)
Definition  qa00120000 :=  (if_then_else_M (tta2 x4 x1 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O  (if_then_else_M (EQ_M (reveal x4) (i 3) ) O     (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 158) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 158)  (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 159) (if_then_else_M (EQ_M (to x4) (i 2)) (grn 159) (if_then_else_M (EQ_M (to x4) (i 3)) acc O))))))))).

(****************qa00000000 -> qa00100000 -> qa00100001->******************************)
(*qa00200001 qa10100001 qa00101001 qa01100001 qa00100101*)

(*Definition qa00200001 := O.
Definition  qa01100001 := (if_then_else_M (EQ_M (to x4) (i 3)) acc    (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 160) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 160) O))).
*)

(*****************///end  qa00100000 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00000010 ///**********************************************)
(***********************************************************************************)



(*****************qa00000000 -> qa00000010 ->  qa00010010 ->**)
(** qa00020010  qa10010010  qa00011010  qa01010010  qa00010110**)
Definition  qa00020010 := (if_then_else_M (tta1 x4 x1 3) mx1rn1 (if_then_else_M (tta1 x4 x2 3) mx2rn2 (if_then_else_M (tta2 x4 x1 x2 4) mx2rn1  (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O   (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 161) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 161)  (if_then_else_M ((EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)) (grn 162) (if_then_else_M (EQ_M (to x4) (i 2)) (grn 162) O))))))))).

(***********qa00000000 -> qa00000010 ->qa00000011->***************************)



(*****************///end   qa00000010 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00010000 ///**********************************************)
(***********************************************************************************)

(**********qa00000000 -> qa00010000 -> qa00020000 -> ***)
(*qa10020000, qa00021000, qa01020000 , qa00020100 , qa00120000 qa00020010*)



Definition  qa01020000  := (if_then_else_M (tta2 x4 x1 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x4) (i 1) ) O (if_then_else_M (EQ_M (reveal x4) (i 2) ) O (if_then_else_M (EQ_M (reveal x4) (i 3) ) O    (if_then_else_M ((EQ_M (to x4) (i 1)) & (EQ_M (act x4) new)) (grn 163) (if_then_else_M (EQ_M (to x4) (i 1)) (grn 163) (if_then_else_M (EQ_M (to x4) (i 2)) acc  (if_then_else_M ((EQ_M (to x4) (i 3)) & (EQ_M (act x4) new)) (grn 164) (if_then_else_M (EQ_M (to x4) (i 3)) (grn 164) O))))))))).



(**qa00000000 -> qa00010000 ->qa01010000 ->***)
(**qa02010000 qa01020000 qa11010000 qa01011000 qa01110000 qa01010010*)


(*****************///end  qa00010000 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00000001 ///**********************************************)
(***********************************************************************************)

(**********qa00000000 -> qa00000001 -> qa10000001 ->*)



(***************qa00000000 -> qa00000001 -> qa00001001 ->**********)

(****qa01001001 qa00001101 qa00101001 qa00001011 *)

(** qa00000000 -> qa00000001 -> qa01000001 ->*)

(*** qa02000001  qa11000001  qa01001001 qa01100001  qa01000011 ****)


(*****************///end  qa00000001 ///**********************************************)
(***********************************************************************************)

(********** qa00000000 -> qa10000000 -> *******)


Definition qa20000000_s :=  (if_then_else_M (tta2 x3 x2 x1 1) qa30000000  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) qa21000000  (if_then_else_M (EQ_M (to x3) (i 2)) qa20000100  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) qa20100000  (if_then_else_M (EQ_M (to x3) (i 3)) qa20000010 (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) qa20010000  (if_then_else_M (EQ_M (to x3) (i 4)) qa20000001 O))))))).
Definition qa11000000_s :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O  (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M (EQ_M (to x3) (i 1))  qa21000000 (if_then_else_M (EQ_M (to x3) (i 2))   qa12000000  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new))  qa11100000  (if_then_else_M (EQ_M (to x3) (i 3))  qa11000010  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new))  qa11010000  (if_then_else_M (EQ_M (to x3) (i 4))  qa11000001 O)))))))))).
Definition qa10000100_s:= (if_then_else_M (tta1 x3 x1 2) qa10000200 (if_then_else_M (tta1 x3 x2 2) qa10000200 (if_then_else_M (EQ_M (to x3) (i 1))  qa20000100  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) qa10100100 (if_then_else_M (EQ_M (to x3) (i 3)) qa10000110  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) qa10010100  (if_then_else_M (EQ_M (to x3) (i 4)) qa10000101 O))))))).

Definition qa10100000_s:= (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M (EQ_M (to x3) (i 1))  acc    (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 30)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 30) (if_then_else_M (EQ_M (to x3) (i 3))  acc  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 31)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 31) O)))))))))).

Definition qa10000010_s := (if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x1 3) mx2rn2 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M (EQ_M (to x3) (i 1))  acc    (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 32)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 32)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 33)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 33) O)))))))))).

Definition qa10010000_s:= (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M (EQ_M (to x3) (i 1))  acc    (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 34)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 34)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 35)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 35) (if_then_else_M (EQ_M (to x3) (i 4))  acc O)))))))))).

Definition qa10000001_s:= (if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x1 4) mx2rn2(if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (to x3) (i 1))  acc    (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 36)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 36)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 37)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 37) O)))))))))).

(***********qa00000000 -> qa00001000 -> *******)



Definition qa01001000_s := (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O (if_then_else_M (EQ_M (to x3) (i 2))  acc  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 38)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 38)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 39)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 39) O)))))))))).

Definition qa00001100_s:= (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1(if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 40)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 40)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 41)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 41) O)))))))))).

Definition qa00101000_s:= (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1(if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 41)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 41) (if_then_else_M (EQ_M (to x3) (i 3))  acc   (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 42)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 42) O)))))))))).


Definition qa00001010_s := (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1(if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x2 3) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O      (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 43)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 43)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 44)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 44) O)))))))))).

Definition qa00011000:=  (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O         (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 45)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 45)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 46)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 46) (if_then_else_M (EQ_M (to x3) (i 4))  acc O))))) ))))).

Definition qa00001001:= (if_then_else_M (tta1 x3 x1 1) mx1rn1 (if_then_else_M (tta1 x3 x2 1) mx2rn1(if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 47)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 47)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 48)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 48) O)))))))))).
Definition qa00002000 := 
(if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 8)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 8) (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 9)  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 9) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 10)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 10) O))))))))).

(*********qa00000000 ->qa01000000-> **********)


Definition qa02000000 := (if_then_else_M (tta2 x3 x1 x2 2) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 49)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 49)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 49)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 49)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 50)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 50) O)))))))))).


Definition qa01100000 :=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O    (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 51)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 51) (if_then_else_M (EQ_M (to x3) (i 2))  acc  (if_then_else_M (EQ_M (to x3) (i 3))  acc (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 52)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 52) O)))))))))).

Definition qa01000010:=  (if_then_else_M (tta1 x3 x1 3) mx1rn1  (if_then_else_M (tta1 x3 x2 3) mx2rn2  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 53)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 53) (if_then_else_M (EQ_M (to x3) (i 2))  acc    (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 54)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 54) O)))))))))).

Definition qa01010000:=  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 55)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 55)  (if_then_else_M (EQ_M (to x3) (i 2))  acc  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 56)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 56)  (if_then_else_M (EQ_M (to x3) (i 4))  acc O)))))) )))).

Definition qa01000001:=  (if_then_else_M (tta1 x3 x1 4) mx1rn1  (if_then_else_M (tta1 x3 x2 4) mx2rn2 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 57)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 57) (if_then_else_M (EQ_M (to x3) (i 2))  acc   (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 58)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 58) O)))))))))).
(**********qa00000000 ->qa00000100->****)


Definition qa00000110 := (if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1(if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x2 3) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 4) ) O    (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 59)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 59)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 60)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 60) O)))))))))).

Definition qa00010100:= (if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1(if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O    (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 61)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 61)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 62)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 62) (if_then_else_M (EQ_M (to x3) (i 4))  acc O)))))))))).

Definition qa00000101:= (if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1(if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 63)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 63)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 64)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 64) O)))))))))).
Definition qa00000200 := (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O  (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 14)  (if_then_else_M (EQ_M (to x2) (i 1)) (grn 14) (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 15)  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 15) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 16)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 16) O))))))))).
(***************qa00000000 ->qa001000000-> *)



Definition qa00200000:=  (if_then_else_M (tta2 x3 x1 x2 3) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O (if_then_else_M (EQ_M (to x3) (i 3))  acc  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 65)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 65) (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 66)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 66)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 67)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 67) O))))))))))).



Definition qa00100100 := (if_then_else_M (tta1 x3 x1 2) mx1rn1 (if_then_else_M (tta1 x3 x2 2) mx2rn1  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O (if_then_else_M (EQ_M (to x3) (i 3))  acc   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 70)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 70)  (if_then_else_M ((EQ_M (to x3) (i 4)) & (EQ_M (act x3) new)) (grn 71)  (if_then_else_M (EQ_M (to x3) (i 4)) (grn 71) O)))))))))).

Definition qa00110000:= (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 72)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 72)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 73)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 73) (if_then_else_M (EQ_M (to x3) (i 3))  acc  (if_then_else_M (EQ_M (to x3) (i 4))  acc  O)))))))))).

Definition qa00100001:=  (if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x2 4) mx2rn1  (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O   (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 74)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 74)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 75)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 75) (if_then_else_M (EQ_M (to x3) (i 3))  acc O)))))))))).

(*******qa00000000 ->  qa00000010->********)

(********resume here******************)


Definition qa00010010:= (if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x2 3) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O    (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 76)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 76)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 77)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 77) (if_then_else_M (EQ_M (to x3) (i 4))  acc O)))))))))).

Definition qa00000011:= (if_then_else_M (tta1 x3 x1 3) mx1rn1 (if_then_else_M (tta1 x3 x2 3) mx2rn1(if_then_else_M (tta1 x3 x1 4) mx1rn1 (if_then_else_M (tta1 x3 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 78)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 78)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 79)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 79) O)))))))))).
Definition  qa00000020 := (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 15)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 15)   (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 16)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 16) (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) (grn 17)  (if_then_else_M (EQ_M (to x2) (i 4)) (grn 17) O))))))))).

(****qa00000000 ->  qa00010000 -> *)


Definition qa00020000 := (if_then_else_M (tta2 x3 x1 x2 4) mx2rn1 (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 80)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 80)  (if_then_else_M ((EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)) (grn 81)  (if_then_else_M (EQ_M (to x3) (i 2)) (grn 81)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 82)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 82) O)))))))))).


(*Definition qa01010000 := (if_then_else_M (EQ_M (reveal x3) (i 1) ) O  (if_then_else_M (EQ_M (reveal x3) (i 2) ) O (if_then_else_M (EQ_M (reveal x3) (i 3) ) O (if_then_else_M (EQ_M (reveal x3) (i 4) ) O  (if_then_else_M (EQ_M (to x3) (i 2))  acc (if_then_else_M (EQ_M (to x3) (i 4))  acc  (if_then_else_M ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) (grn 83)  (if_then_else_M (EQ_M (to x3) (i 1)) (grn 83)  (if_then_else_M ((EQ_M (to x3) (i 3)) & (EQ_M (act x3) new)) (grn 84)  (if_then_else_M (EQ_M (to x3) (i 3)) (grn 84) O)))))))))).
*)


(********* qa00000000 ->  qa00000001 ->*********)
Definition qa00000002 :=   (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) (grn 21)  (if_then_else_M (EQ_M (to x2) (i 1)) (grn 21)  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) (grn 22)  (if_then_else_M (EQ_M (to x2) (i 2)) (grn 22)  (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) (grn 23 )  (if_then_else_M (EQ_M (to x2) (i 3)) (grn 23) O ))))))))).



(*****************************************************************************)
(*****************************************************************************)



Definition qa10000000_s :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M (EQ_M (to x2) (i 1))  qa20000000  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new))  qa11000000  (if_then_else_M (EQ_M (to x2) (i 2))  qa10000100(if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new))  qa10100000  (if_then_else_M (EQ_M (to x2) (i 3))  qa10000010 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new))  qa10010000  (if_then_else_M (EQ_M (to x2) (i 4))  qa10000001 O))))))))))).

Definition qa00001000_s :=  (if_then_else_M (tta1 x2 x1 1) qa00002000 (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) qa01001000  (if_then_else_M (EQ_M (to x2) (i 2)) qa00001100 (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa00101000 (if_then_else_M (EQ_M (to x2) (i 3)) qa00001010 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa00011000  (if_then_else_M (EQ_M (to x2) (i 4)) qa00001001 O)))))))))).


Definition qa01000000_s :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O  (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa11000000  (if_then_else_M (EQ_M (to x2) (i 2)) qa02000000 (if_then_else_M (EQ_M (to x2) (i 1)) qa01001000  (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa01100000  (if_then_else_M (EQ_M (to x2) (i 3)) qa01000010 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa01010000  (if_then_else_M (EQ_M (to x2) (i 4)) qa01000001 O))))))))))).

 Definition qa00000100_s :=  (if_then_else_M (EQ_M (reveal x2) (i 2) ) & (EQ_M (to x1) (i 2)) qa00000200 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O  (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa10000100  (if_then_else_M (EQ_M (to x2) (i 1)) qa00001100 (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa00100100  (if_then_else_M (EQ_M (to x2) (i 3)) qa00000110 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa00010100  (if_then_else_M (EQ_M (to x2) (i 4)) qa00000101 O)))))))))).

 Definition qa00100000_s :=  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O   (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa10100000  (if_then_else_M (EQ_M (to x2) (i 1)) qa00101000  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) qa01100000 (if_then_else_M (EQ_M (to x2) (i 2)) qa00100100(if_then_else_M (EQ_M (to x2) (i 3)) qa00200000 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa00110000  (if_then_else_M (EQ_M (to x2) (i 4)) qa00100001 O))))))))))).

Definition  qa00000010_s  :=   (if_then_else_M (EQ_M (reveal x2) (i 3) ) & (EQ_M (to x1) (i 3))  qa00000020 (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new))  qa10000010 (if_then_else_M (EQ_M (to x2) (i 4))  qa00001010   (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new))  qa01000010  (if_then_else_M (EQ_M (to x2) (i 2))  qa00000110 (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new))  qa00010010  (if_then_else_M (EQ_M (to x2) (i 4))  qa00000011 O)))))))))).

Definition  qa00010000_s  :=    (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O    (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa10010000  (if_then_else_M (EQ_M (to x2) (i 1)) qa00011000  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) qa01010000 (if_then_else_M (EQ_M (to x2) (i 2)) qa00010100  (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa00110000  (if_then_else_M (EQ_M (to x2) (i 3)) qa00010010 (if_then_else_M (EQ_M (to x2) (i 4)) qa00020000 O))))))))))).
Definition  qa00000001_s := (if_then_else_M (EQ_M (reveal x2) (i 4) ) & (EQ_M (to x1) (i 4))  qa00000002  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O  (if_then_else_M (EQ_M (reveal x2) (i 2) ) O   (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new))  qa10000001  (if_then_else_M (EQ_M (to x2) (i 1))  qa00001001  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new))  qa01000001  (if_then_else_M (EQ_M (to x2) (i 2))  qa00000101 (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new))  qa00100001 (if_then_else_M (EQ_M (to x2) (i 3))  qa00000011  O)))))))))).



Definition t14 := msg  (if_then_else_M (EQ_M (reveal x2) (i 1) ) O (if_then_else_M (EQ_M (reveal x2) (i 2) ) O  (if_then_else_M (EQ_M (reveal x2) (i 3) ) O (if_then_else_M (EQ_M (reveal x2) (i 4) ) O (if_then_else_M ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) qa10000000_s  (if_then_else_M (EQ_M (to x2) (i 1)) qa00001000_s  (if_then_else_M ((EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)) qa01000000_s  (if_then_else_M (EQ_M (to x2) (i 2)) qa00000100_s (if_then_else_M ((EQ_M (to x2) (i 3)) & (EQ_M (act x2) new)) qa00100000_s  (if_then_else_M (EQ_M (to x2) (i 3))  qa00000010_s (if_then_else_M ((EQ_M (to x2) (i 4)) & (EQ_M (act x2) new)) qa00010000_s  (if_then_else_M (EQ_M (to x2) (i 4))  qa00000001_s O)) ))) ) )))))).
Definition phi3:= phi2 ++ [t14].

(**************************************@@@@phi5@@@*********************************************************)
(**********************************************************************************************************)



Definition mphi4 := (conv_mylist_listm phi4).
Definition x5 := (f mphi4).


(************/// start qa10000000/// ***************)

(********************************start qa20000000******************************)

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> *********)
(** qa22000000  qa21100000  qa21000010  qa21010000 qa21000001 *)

Definition qa22000000 :=  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 165) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 165)  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 1656) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 166) O) ))).


Definition qa21100000 := (if_then_else_M (EQ_M (to x5) (i 2))  acc  (if_then_else_M (EQ_M (to x5) (i 3))  acc  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 167) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 167) O) ))).

Definition   qa21000010 := (if_then_else_M (EQ_M (to x5) (i 2))  acc   (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 168) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 168) O) )).

Definition  qa21010000 :=  (if_then_else_M (EQ_M (to x5) (i 2))  acc  (if_then_else_M (EQ_M (to x5) (i 3))  acc    (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 168) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 168) O) ))).

Definition  qa21000001 := (if_then_else_M (EQ_M (to x5) (i 2))  acc    (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 169) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 169) O) )).


(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->*****************************************)
(** qa20100100  qa20000110  qa20010100  qa20000101*)

Definition qa20100100  :=  (if_then_else_M (EQ_M (to x5) (i 3))  acc    (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 170) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 170) O) )).

Definition  qa20000110 :=     (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 171) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 171) O) ).
Definition  qa20010100  :=   (if_then_else_M (EQ_M (to x5) (i 4))  acc    (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 172) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 172) O) )).
Definition  qa20000101 :=      (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 173) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 173) O) ).

(****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->*************)
(**qa20200000 qa21100000 qa20100100  qa20110000 qa20100001*)
Definition qa20200000 :=(if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 174) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 174) (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 175) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 175) O) ))).

Definition   qa20110000 :=(if_then_else_M (EQ_M (to x5) (i 3))  (grn 176) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 177) (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 178) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 178) O) ))).

Definition  qa20100001 := (if_then_else_M (EQ_M (to x5) (i 3))  (grn 179)  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 179) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 179) O) )).

(************************qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 ->*************)
(***qa21000010 qa20000110 qa20010010 qa20000011****************************************************)

Definition  qa20010010 := (if_then_else_M (EQ_M (to x5) (i 4)) (grn 180) (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 181) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 181) O) )).
Definition  qa20000011 :=  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 182) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 182) O) ).

(*******************qa00000000 -> qa10000000 -> qa20000000 ->qa20010000->******************)
(**qa20020000 qa21010000 qa20010100 qa20110000 qa20010010 **************)
Definition qa20020000 :=  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 183) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 183)  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 184) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 184) O) )) ).


(**************qa00000000 -> qa10000000 -> qa20000000 -> qa20000001-> ***************************************)
(**  qa21000001  qa20000101  qa20100001  qa20000011*********)


(***********************end  qa20000000********************************)


(*************************start  qa11000000 **************************)

(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 -> *)


Definition  qa12100000 :=
 (if_then_else_M (EQ_M (to x5) (i 1)) (grn 185) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 186)  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 187) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 187) O) )) ).
Definition  qa12000010 :=    (if_then_else_M (EQ_M (to x5) (i 1)) (grn 188)  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 189) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 189) O) )) .
Definition  qa12010000 :=  (if_then_else_M (EQ_M (to x5) (i 1)) (grn 190) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 191)  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 192) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 192) O) )) ).
Definition  qa12000001 :=  (if_then_else_M (EQ_M (to x5) (i 1)) (grn 193) (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 194) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 194) O) ) ).
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000->******************)

(**qa21100000 qa12100000 qa11200000 qa11110000 qa11100001*)

Definition  qa11200000 := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 195) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 196)  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 197) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 197) O) )) ).
Definition  qa11110000 :=(if_then_else_M (EQ_M (to x5) (i 1)) (grn 198) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 199)  (if_then_else_M (EQ_M (to x5) (i 3)) (grn 200) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 201)  O) )) ).
Definition  qa11100001 := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 202) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 202)  (if_then_else_M (EQ_M (to x5) (i 3)) (grn 203) O ))).
(*************qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 -> ****************)

Definition   qa11010010 := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 204) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 205) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 206)   O) ) ).

Definition   qa11000011 :=  (if_then_else_M (EQ_M (to x5) (i 1)) (grn 207) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 208)    O) ).

(**************qa00000000 -> qa10000000 -> qa11000000 ->qa11010000-> ***********)

Definition  qa11020000 := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 209) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 209)  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 210) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 210) O) ) )).

(****************************************qa00000000 -> qa10000000 -> qa11000000 -> qa11000001-> *)
(****qa21000001 qa12000001 qa11100001 qa11000011 *)


(*****************end qa11000000 **********************************************)

(****************start qa10000100 ********************************************)

(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->  *)
(**  qa20100100  qa10200100   qa10110100  qa10100101 *)

Definition   qa10200100 :=  (if_then_else_M (EQ_M (to x5) (i 1)) (grn 211)  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 212) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 212) O) ) ).
Definition    qa10110100 :=   (if_then_else_M (EQ_M (to x5) (i 1)) (grn 213) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 214)  (if_then_else_M (EQ_M (to x5) (i 4)) (grn 215)   O) ) ).
Definition  qa10100101 :=  (if_then_else_M (EQ_M (to x5) (i 1)) (grn 216) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 217)   O) ).
(***************  qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 ->*********)

(****  qa20000110  qa10010110  qa10000111   *)

Definition  qa10010110  := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 218)  (if_then_else_M (EQ_M (to x5) (i 4)) (grn 219)   O) ).
Definition  qa10000111  := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 220)  O) .
(****************************** qa00000000 ->  qa10000000 -> qa10000100 -> qa10010100->*************************)
(* qa20010100  qa10020100  qa10110100  qa10010110  *)

Definition  qa10020100 :=  (if_then_else_M (EQ_M (to x5) (i 1)) (grn 221)   (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 222) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 222) O) ) ).


(*** qa00000000 ->  qa10000000 -> qa10000100 ->qa10000101->*****)



(******************end   qa10000100 ***********************)

(*****************************start qa10100000 **********)


(******** qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 ->   *)

(**  qa20200000 qa11200000 qa10200100 qa10210000 qa10200001 *)

Definition  qa10210000 := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 223)  (if_then_else_M (EQ_M (to x5) (i 4)) (grn 224)   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 225) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 225) O) ) )).
Definition  qa10200001 := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 226)    (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 227) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 227) O) ) ).

(******************qa00000000 -> qa10000000 -> qa10100000 -> qa10110000->*)
(*  qa20110000  qa10210000  qa10120000  qa11110000  qa10110100*)

Definition   qa10120000 := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 228)  (if_then_else_M (EQ_M (to x5) (i 3)) (grn 229)   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 230) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 230) O) ) )).


(***qa00000000 -> qa10000000 -> qa10100000 ->qa10100001->***)

(***qa20100001 qa10200001 qa11100001 qa10100101 *)

(*****************************end qa10100000 **********)


(*****************************start qa10000010 **********)

(******** qa00000000 -> qa10000000 -> qa10000010 -> qa10010010 ->  *)


(** qa20010010 qa10020010 qa11010010 qa10010110 *)

(*Definition  qa20010010  := O. *)
Definition  qa10020010 :=  (if_then_else_M (EQ_M (to x5) (i 1)) (grn 231)   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 232) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 232) O) ) ).


(******* qa00000000 -> qa10000000 -> qa10000010 ->qa1000001->1***)
(**qa20000011 qa11000011 qa10000111 *)


(*****************************end qa10000010 **********)

(*****************************start qa10010000 **********)

(******** qa00000000 ->  qa10000000 -> qa10010000 -> qa20010000 -> ***)
(** qa20020000  qa21010000  qa20010100  qa20110000 qa20010010  *)


(******** qa00000000 ->  qa10000000 -> qa10010000 -> qa10020000 -> ***)
(** qa20020000  qa11020000  qa10020100  qa10120010  *)


(************qa00000000 ->  qa10000000 -> qa10010000 -> qa11010000 -> *)
(*** qa21010000 qa12010000 qa11020000 qa11110000 qa11010010*)



(************qa00000000 ->  qa10000000 -> qa10010000 -> qa10010100 -> *)
(*qa20010100 qa10020100 qa10110100 qa10010110*)


(************qa00000000 ->  qa10000000 -> qa10010000 -> qa10110000 -> *)
(* qa20110000  qa10210000  qa10120000  qa11110000  qa10110100 *)


(************qa00000000 ->  qa10000000 -> qa10010000 -> qa10010010 -> *)
(*qa20010010 qa10020010 qa11010010 qa10010110 *)



(*****************************end qa10010000 **********)


(*****************************start qa10000001 **********)


(********qa00000000 -> qa10000000 -> qa10000001 -> qa20000001 -> **********)
(**qa21000001 qa20000101 qa20100001 qa20000011  *)


(********qa00000000 -> qa10000000 -> qa10000001 -> qa11000001 -> **********)
(** qa21000001  qa12000001  qa11100001  qa11000011   *)

(********qa00000000 -> qa10000000 -> qa10000001 -> qa10000101 -> **********)
(** qa20000101 qa10100101 qa10000111   *)



(********qa00000000 -> qa10000000 -> qa10000001 -> qa10100001 -> **********)

(**qa20100001  qa10200001 qa11100001 qa10100101**)

 

(********qa00000000 -> qa10000000 -> qa10000001 -> qa10000011 -> **********)
(***qa20000011 qa11000011 qa10000111 *)



(********************end qa10000001 **********************************)


(************/// end qa10000000/// ***************)

(**********************************************************************************************)

(************/// start qa00001000/// ***************)

(****************************start qa01001000 **********)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> *)
 
Definition qa02101000 :=   (if_then_else_M (EQ_M (to x5) (i 3)) (grn 234)   (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 235) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 235) O) ) ).
Definition  qa02001010 :=     (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 236) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 236) O) ) .
Definition qa02011000 := (if_then_else_M (EQ_M (to x5) (i 4)) (grn 237) (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 238) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 238) O)))  .
Definition qa02001001 := (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 239) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 239) O) ) .

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 -> *)
(*
Definition qa02101000 :=(if_then_else_M (EQ_M (to x5) (i 3)) (grn 240) (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 241) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 241) O)))  .*)
Definition  qa01201000 := (if_then_else_M (EQ_M (to x5) (i 2)) (grn 240) (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 241) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 241) O)))  .
Definition  qa01111000 := (if_then_else_M (EQ_M (to x5) (i 1)) (grn 242) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 243) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 244)  O)))  .
Definition  qa01101001 :=  (if_then_else_M (EQ_M (to x5) (i 1)) (grn 245) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 246) O)).


(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 -> *)
(*
 Definition qa02001010  := (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 247) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 247) O))  .*)
 Definition qa01011010  := (if_then_else_M (EQ_M (to x5) (i 2)) (grn 242) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 243) O))  .
Definition  qa01001011 := (if_then_else_M (EQ_M (to x5) (i 2)) (grn 242)  O)  .


(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01011000 -> *)
(*
Definition qa02011000 :=  O. *)
Definition qa01021000 :=   (if_then_else_M (EQ_M (to x5) (i 2)) (grn 243) (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 244) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 244) O)))  .
(*
Definition qa01111000 := O. 
Definition qa01011010 := O.*)
(***qa00000000 -> qa00001000 ->  qa01001000 ->   qa01001001-> *)
(*
Definition  qa02001001 := O.  
Definition   qa01101001 := O. 
Definition  qa01001001 := O.*)
(****************************end qa01001000 **********)

(*************************start qa00001100 ************)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> *)

Definition qa00201100  := (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 245) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 245) O)).
Definition qa00111100 :=  (if_then_else_M (EQ_M (to x5) (i 3)) (grn 246)  (if_then_else_M (EQ_M (to x5) (i 4)) (grn 247) O)).
Definition qa00101101 :=  (if_then_else_M (EQ_M (to x5) (i 3)) (grn 248) O).
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001110 -> *)

Definition qa00011110 :=  (if_then_else_M (EQ_M (to x5) (i 4)) (grn 249) O).
Definition qa00001111 := O.

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00011100 -> *)

Definition   qa00021100  := (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 250) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 250) O)).

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001101 -> *)




(************** end qa00001100 ************)
(*************************start  qa00101000 ************)
(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 -> *)

Definition qa00211000 := (if_then_else_M (EQ_M (to x5) (i 4)) (grn 251) (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 252) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 252) O))).
Definition qa00201001 := (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 253) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 253) O)).

(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00111000 -> *)
(*Definition qa00211000 := O.*)
Definition qa00121000  := (if_then_else_M (EQ_M (to x5) (i 3)) acc (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 254) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 254) O))).


(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00101001 -> *)


(*************************end  qa00101000 ********)
(*********************start qa00001010 ************)

(***qa00000000 -> qa00001000 ->  qa00001010 ->  qa00011010 -> *)


Definition  qa00021010  :=  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) (grn 255) (if_then_else_M (EQ_M (to x5) (i 3)) (grn 255) O)).

 

(***********end qa00001010 ************)
(***********************start qa00011000 ****)

(***qa00000000 -> qa00001000 ->  qa00011000 -> qa00021000 -> *)

(***********************end qa00011000 ****)
(*********commented out qa00001001**********)

(************/// end qa00001000/// ***************)

(************/// start qa01000000/// ***************)

(******* start qa02000000 ************)

(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> *)

Definition qa02200000  := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 256) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 256) (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (grn 257) (if_then_else_M (EQ_M (to x5) (i 4)) (grn 257) O)))).

Definition qa02110000 := (if_then_else_M (EQ_M (to x5) (i 3)) acc (if_then_else_M (EQ_M (to x5) (i 4)) acc  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 258) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 258) O)))).
(*Definition qa02100001 := O. *)

(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 -> *)

Definition qa02010010 :=  (if_then_else_M (EQ_M (to x5) (i 4)) acc  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 259) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 259) O))).
Definition qa02000011 :=  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 260) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 260) O)).

(***qa00000000 ->  qa01000000 ->  qa02000000 ->qa02010000 -> *)
Definition qa02020000 := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 261) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 261) (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 262) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 262) O)))).

(***qa00000000 ->  qa01000000 ->  qa02000000 ->qa02000001 -> *)

(******* end qa02000000 ************)
(******* start qa01100000 ************)
(*qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->*)

Definition qa01210000 :=  (if_then_else_M (EQ_M (to x5) (i 2)) acc (if_then_else_M (EQ_M (to x5) (i 4)) acc  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 263) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 263) O)))).
Definition qa01200001 :=  (if_then_else_M (EQ_M (to x5) (i 2)) acc  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 264) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 264) O))).

(*qa00000000 -> qa01000000 -> qa01100000 ->  qa01110000 ->*)

Definition  qa01120000 := (if_then_else_M (EQ_M (to x5) (i 2)) acc (if_then_else_M (EQ_M (to x5) (i 3)) acc  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 265) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 265) O)))).


(*qa00000000 -> qa01000000 -> qa01100000 -> qa01100001 ->*)


(******* end qa01100000 ************)
(******* start qa01000010************)
(*qa00000000 -> qa01000000 ->qa01000010 -> qa01010010 -> **)

Definition qa01020010 := (if_then_else_M (EQ_M (to x5) (i 2)) acc  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 266) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 266) O))).



(*qa00000000 -> qa01000000 ->qa01000010 ->  qa01000011-> **)

(******* end qa01000010************)

(**********qa01000001 commented out***********)
(************/// end qa01000000/// ***************)
(************/// start qa00000100/// ***************)
(*******start qa00000110************)

(*qa00000000 -> qa00000100 ->  qa00000110 -> qa00010110 -> **)

Definition qa00020110 :=  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 267) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 267)  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 268) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 268) O)))).


(*qa00000000 -> qa00000100 ->  qa00000110 -> qa00000111 -> **)

(*******end qa00000110************)
(*********start qa00010100 ****************************)

(*qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 -> **)

Definition  qa00120100 :=  (if_then_else_M (EQ_M (to x5) (i 3)) acc  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 269) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 269) O))).


Definition qa00210100 := (if_then_else_M (EQ_M (to x5) (i 4)) acc  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 270) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 270) O))).

(*********end qa00010100 ****************************)
(********start qa00000101 **************************)
(*qa00000000 -> qa00000100 ->  qa00000101-> qa00100101 -> **)

Definition qa00200101 := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 271) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 271) O)).

(********end qa00000101 **************************)


(************/// end qa00000100/// ***************)

(************/// start qa00100000/// ***************)
(******* start qa00200000************)

(*qa00000000 ->  qa00100000  -> qa00200000 -> qa00200100 -> **)


Definition qa00220000 := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 272) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 272) (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) (grn 273) (if_then_else_M (EQ_M (to x5) (i 2)) (grn 273) O)))).

(*qa00000000 ->  qa00100000  -> qa00200000 ->  qa00200001 -> **)

(*******end  qa00200000***)
(*****qa00100100 *****commented out**********)

(**start qa00110000****************************)
(*qa00000000 ->  qa00100000  ->  qa00110000 ->qa00120000 ->*)

(**end qa00110000****************************)
(*****start qa00100001**********************)
(*qa00000000 ->  qa00100000  ->   qa00100001 ->qa02100001 ->*)

Definition qa02200001 := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 274) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 274) O)).
Definition qa12100001 := (if_then_else_M (EQ_M (to x5) (i 1)) acc (if_then_else_M (EQ_M (to x5) (i 3)) acc O)).
Definition qa02101001 :=  (if_then_else_M (EQ_M (to x5) (i 3)) acc (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) (grn 275) (if_then_else_M (EQ_M (to x5) (i 1)) (grn 275) O))).

(*****end qa00100001**********************)

(************/// end qa00000010/// ***************)


(************/// start qa00010000/// ***************)
(**********************start qa00020000 ****************)


(**********************stop qa00020000 ****************)
(************/// end qa00010000/// ***************)


(************/// start qa00000001/// ***************)
(*********start  qa10000001  ***********************)
(*qa00000000 ->  qa00000001 -> qa10000001 ->  qa10100001  ->*)


(********end qa10000001 ***************************)
(************/// end qa00000001/// ***************)

 (*************qa00000000 -> qa10000000 -> qa20000000 -> *)

Definition qa21000000_s:=   (if_then_else_M (EQ_M (to x5) (i 2))   qa22000000  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa21100000 (if_then_else_M (EQ_M (to x5) (i 3)) qa21000010  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa21010000  (if_then_else_M (EQ_M (to x5) (i 4)) qa21000001 O))))).

Definition qa20000100_s :=  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa20100100 (if_then_else_M (EQ_M (to x5) (i 3)) qa20000110   (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa20010100  (if_then_else_M (EQ_M (to x5) (i 4))  qa20000101 O)))).


Definition qa20100000_s := (if_then_else_M (EQ_M (to x5) (i 3))  qa20200000  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))  qa21100000  (if_then_else_M (EQ_M (to x5) (i 2))  qa20100100  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa20110000  (if_then_else_M (EQ_M (to x5) (i 4)) qa20100001 O))))).

Definition qa20000010_s :=    (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))  qa21000010  (if_then_else_M (EQ_M (to x5) (i 2)) qa20000110  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa20010010  (if_then_else_M (EQ_M (to x5) (i 4)) qa20000011 O)))).
Definition qa20010000_s := (if_then_else_M (EQ_M (to x5) (i 4)) qa20020000   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa21010000  (if_then_else_M (EQ_M (to x5) (i 2)) qa20010100   (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa20110000 (if_then_else_M (EQ_M (to x5) (i 3)) qa20010010   O))))).

Definition qa20000001_s :=    (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa21000001  (if_then_else_M (EQ_M (to x5) (i 2)) qa20000101  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa20100001  (if_then_else_M (EQ_M (to x5) (i 3))  qa20000011 O)))).

(*******************************qa00000000 -> qa10000000 ->qa11000000 ->*******************)


Definition qa12000000_s := (if_then_else_M (EQ_M (to x5) (i 1)) qa22000000 (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa12100000  (if_then_else_M (EQ_M (to x5) (i 3))  qa12000010  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa12010000  (if_then_else_M (EQ_M (to x5) (i 4)) qa12000001 O))))).


Definition  qa11100000_s :=  (if_then_else_M (EQ_M (to x5) (i 1)) qa21100000 (if_then_else_M (EQ_M (to x5) (i 2))  qa12100000  (if_then_else_M (EQ_M (to x5) (i 3))  qa11200000 (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa11110000  (if_then_else_M (EQ_M (to x5) (i 4)) qa11100001 O))))).

Definition  qa11000010_s :=  (if_then_else_M (EQ_M (to x5) (i 1))  qa21000010  (if_then_else_M (EQ_M (to x5) (i 2))   qa12000010  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa11010010  (if_then_else_M (EQ_M (to x5) (i 4))  qa11000011 O)))).
Definition qa11010000_s :=   (if_then_else_M (EQ_M (to x5) (i 1)) qa21010000 (if_then_else_M (EQ_M (to x5) (i 2)) qa12010000  (if_then_else_M (EQ_M (to x5) (i 4)) qa11020000  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa11110000  (if_then_else_M (EQ_M (to x5) (i 3))  qa11010010 O))))).


(************************qa00000000 -> qa10000000 -> qa10000100 ->***************************)

(*******************qa20000100, qa10100100, qa10000110, qa10010100, qa10000101*****************************)

Definition qa10100100_s := (if_then_else_M (EQ_M (to x5) (i 1))   qa20100100  (if_then_else_M (EQ_M (to x5) (i 3)) qa10200100     (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa10110100  (if_then_else_M (EQ_M (to x5) (i 4)) qa10100101 O)))).


Definition qa10000110_s :=   (if_then_else_M (EQ_M (to x5) (i 1))   qa20000110     (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa10010110  (if_then_else_M (EQ_M (to x5) (i 4)) qa10000111 O))).

Definition  qa10010100_s :=   (if_then_else_M (EQ_M (to x5) (i 1))  qa20010100  (if_then_else_M (EQ_M (to x5) (i 4)) qa10020100   (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa10110100   (if_then_else_M (EQ_M (to x5) (i 3)) qa10010110 O)))).
Definition qa10000101_s :=   (if_then_else_M (EQ_M (to x5) (i 1))  qa20000101     (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa10100101  (if_then_else_M (EQ_M (to x5) (i 3)) qa10000111 O))).

(***************************qa00000000 -> qa10000000 ->qa10100000->************************************************)
(*qa20100000, qa10200000, qa11100000, qa10100100, qa10110000, qa10100001*********)


Definition qa10200000_s :=(if_then_else_M (EQ_M (to x5) (i 1))  qa20200000 (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa11200000  (if_then_else_M (EQ_M (to x5) (i 2))  qa10200100 (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa10210000  (if_then_else_M (EQ_M (to x5) (i 4))  qa10200001 O))))).

Definition  qa10110000_s := (if_then_else_M (EQ_M (to x5) (i 1))  qa20110000 (if_then_else_M (EQ_M (to x5) (i 3)) qa10210000  (if_then_else_M (EQ_M (to x5) (i 4)) qa10120000  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa11110000  (if_then_else_M (EQ_M (to x5) (i 2)) qa10110100  O))))).

Definition  qa10100001_s := (if_then_else_M (EQ_M (to x5) (i 1))  qa20100001  (if_then_else_M (EQ_M (to x5) (i 3)) qa10200001  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa11100001  (if_then_else_M (EQ_M (to x5) (i 2))  qa10100101 O)))).


(*****************************************qa00000000 -> qa10000000 ->qa10000010 -> ******************************************************************)
(****qa20000010, qa11000010, qa10000110, qa10010010,qa10000011****)

Definition  qa10010010_s := (if_then_else_M (EQ_M (to x5) (i 1))  qa20010010 (if_then_else_M (EQ_M (to x5) (i 4))  qa10020010  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))  qa11010010  (if_then_else_M (EQ_M (to x5) (i 2))  qa10010110 O)))).

Definition qa10000011_s :=  (if_then_else_M (EQ_M (to x5) (i 1))  qa20000011 (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa11000011  (if_then_else_M (EQ_M (to x5) (i 2)) qa10000111 O))).

(**************qa00000000 -> qa10000000 -> qa10010000 ->****************)
(****qa20010000,qa10020000, qa11010000, qa10010100, qa10110000,qa10010010****)


Definition qa10020000_s :=  (if_then_else_M (EQ_M (to x5) (i 1))  qa20020000  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa11020000  (if_then_else_M (EQ_M (to x5) (i 2))  qa10020100 (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa10120000  (if_then_else_M (EQ_M (to x5) (i 3)) qa10020010 O))))).




(************************qa00000000 -> qa10000000 -> qa10000001 -> ******************************)
(****** qa20000001,  qa11000001  qa10000101 qa10100001 qa10000011 **)

Definition   qa11000001_s := (if_then_else_M (EQ_M (to x5) (i 1))   qa21000001  (if_then_else_M (EQ_M (to x5) (i 2)) qa12000001 (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa11100001  (if_then_else_M (EQ_M (to x5) (i 3)) qa11000011 O)))).

(*************************qa00000000 -> qa00001000 -> qa01001000 ->******************************)
(*******qa01001000**************************************)
(*qa02001000 qa01101000 qa01001010 qa01011000 qa01001001 *)


Definition qa02001000_s :=  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))   qa02101000   (if_then_else_M (EQ_M (to x5) (i 3))  qa02001010 (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa02011000  (if_then_else_M (EQ_M (to x5) (i 4))  O O)))).

Definition  qa01101000_s :=  (if_then_else_M (EQ_M (to x5) (i 2))  qa02101000  (if_then_else_M (EQ_M (to x5) (i 3))  qa01201000  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa01111000  (if_then_else_M (EQ_M (to x5) (i 4))  qa01101001 O)))). 
Definition  qa01001010_s :=  (if_then_else_M (EQ_M (to x5) (i 2))  qa02001010 (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa01011010  (if_then_else_M (EQ_M (to x5) (i 4)) qa01001011 O))). 
Definition  qa01011000_s :=  (if_then_else_M (EQ_M (to x5) (i 2)) qa02011000  (if_then_else_M (EQ_M (to x5) (i 4)) qa01021000  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa01111000  (if_then_else_M (EQ_M (to x5) (i 3)) qa01011010 O)))). 
Definition  qa01001001_s :=  (if_then_else_M (EQ_M (to x5) (i 2))  qa02001001    (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa01101001  (if_then_else_M (EQ_M (to x5) (i 3)) qa01001001 O))).



(*********** qa00000000 -> qa00001000 ->qa00001100 -> ****)
(*qa00101100 qa00001110 qa00011100 qa00001101 *************)


Definition qa00101100_s := (if_then_else_M (EQ_M (to x5) (i 3))  qa00201100   (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa00111100  (if_then_else_M (EQ_M (to x5) (i 4)) qa00101101 O))).
Definition   qa00001110_s :=  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa00011110  (if_then_else_M (EQ_M (to x5) (i 4))  qa00001111 O)).
Definition  qa000011100_s := (if_then_else_M (EQ_M (to x5) (i 4))  qa00021100  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00111100  (if_then_else_M (EQ_M (to x5) (i 3))  qa00111100 O))).

Definition  qa00001101_s :=   (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00101101  (if_then_else_M (EQ_M (to x5) (i 3)) qa00001111 O)).

(**** qa00000000 -> qa00001000 -> qa00101000 -> **************************)

(***qa00201000 qa01101000 qa00101100 qa00111000 qa00101001****)

Definition qa00201000_s := (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01201000  (if_then_else_M (EQ_M (to x5) (i 2)) qa00201100  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa00211000 (if_then_else_M (EQ_M (to x5) (i 4)) qa00201001 O)))).

Definition  qa00111000_s :=  (if_then_else_M (EQ_M (to x5) (i 3)) qa00211000  (if_then_else_M (EQ_M (to x5) (i 4)) qa00121000  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01111000  (if_then_else_M (EQ_M (to x5) (i 2)) qa00111100 O)))).
Definition  qa00101001_s :=   (if_then_else_M (EQ_M (to x5) (i 3)) qa00201001   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01101001  (if_then_else_M (EQ_M (to x5) (i 2)) qa00101101 O))).

(***** qa00000000 -> qa00001000 -> qa00001010 ->********************************)
(*** qa01001010  qa00001110  qa00011010  qa00001011 *)

Definition  qa00011010_s := (if_then_else_M (EQ_M (to x5) (i 4))  qa00021010   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))  qa01011010  (if_then_else_M (EQ_M (to x5) (i 2)) qa00011110  O))).
Definition  qa00001011_s  :=  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa01001011  (if_then_else_M (EQ_M (to x5) (i 3)) qa00001111 O)).


(*********qa00000000 -> qa00001000 ->qa00011000 ->******************************)
(***qa00021000 qa01011000 qa00011100 qa00111000 qa00011010 *)

Definition qa00021000_s := (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01021000  (if_then_else_M (EQ_M (to x5) (i 2)) qa00021100  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa00121000  (if_then_else_M (EQ_M (to x5) (i 4)) qa00021010 O)))).

(***********qa00000000 -> qa00001000 ->qa00001001->********************************)

(********qa01001001 qa00001101 qa00101001 qa00001011***)

(****************************qa00000000 -> qa01000000 -> qa02000000 ->*****************)
(**qa12000000, qa02001000, qa02100000, qa02000010, qa02010000, qa02000001************)

Definition  qa02100000_s :=  (if_then_else_M (EQ_M (to x5) (i 3)) qa02200000 (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa12100000  (if_then_else_M (EQ_M (to x5) (i 3)) qa02101000 (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa02110000  (if_then_else_M (EQ_M (to x5) (i 4)) qa02100001 O))))).
Definition  qa02000010_s := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa12000010 (if_then_else_M (EQ_M (to x5) (i 1)) qa02001010  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa02010010  (if_then_else_M (EQ_M (to x5) (i 4))  qa02000011 O)))).
Definition  qa02010000_s :=  (if_then_else_M (EQ_M (to x5) (i 4))  qa02020000 (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))qa12010000  (if_then_else_M (EQ_M (to x5) (i 1)) qa02011000 (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa02110000  (if_then_else_M (EQ_M (to x5) (i 3)) qa02010010 O))))).
Definition  qa02000001_s := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa12000001  (if_then_else_M (EQ_M (to x5) (i 1)) qa02001001  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa02100001  (if_then_else_M (EQ_M (to x5) (i 3)) qa02000011 O)))).

(***************qa00000000 -> qa01000000 -> qa01100000 ->***********************)
(**qa02100000, qa01200000, qa11100000, qa01101000, qa01110000, qa01100001************)

Definition  qa01200000_s :=  (if_then_else_M (EQ_M (to x5) (i 2))  qa02200000 (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa11200000  (if_then_else_M (EQ_M (to x5) (i 1)) qa01201000  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa01210000  (if_then_else_M (EQ_M (to x5) (i 4))qa01200001 O))))).

Definition  qa01110000_s :=  (if_then_else_M (EQ_M (to x5) (i 2)) qa02110000 (if_then_else_M (EQ_M (to x5) (i 3)) qa01210000 (if_then_else_M (EQ_M (to x5) (i 4)) qa01120000  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa11110000  (if_then_else_M (EQ_M (to x5) (i 1)) qa01111000  O))))).


Definition  qa01100001_s := (if_then_else_M (EQ_M (to x5) (i 2)) qa02100001 (if_then_else_M (EQ_M (to x5) (i 3)) qa01200001   (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa11100001  (if_then_else_M (EQ_M (to x5) (i 1)) qa01101001  O)))).
 
(****************************qa00000000 -> qa01000000 ->qa01000010 ->**************************************)



Definition  qa01010010_s :=  (if_then_else_M (EQ_M (to x5) (i 2)) qa02010010 (if_then_else_M (EQ_M (to x5) (i 4)) qa01020010  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa11010010 (if_then_else_M (EQ_M (to x5) (i 1)) qa01011010  O)))).
Definition  qa01000011_s :=  (if_then_else_M (EQ_M (to x5) (i 2))  qa02000011  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa11000011 (if_then_else_M (EQ_M (to x5) (i 1)) qa01001011   O))).

(************************qa00000000 -> qa01000000 -> qa01000001 ->*******************)
(*  qa02000001,  qa11000001,  qa01001001 ,  qa01100001,  qa01000011**************)

 (*****************///end qa01000000///**********************************************)
(***********************************************************************************)


(*****************///start qa00000100///**********************************************)
(***********************************************************************************)


 (*****************************qa00000000 -> qa00000100 -> qa00000110 ->********************************)
(* qa10000110, qa00001110 , qa00010110, qa00000111*)

Definition  qa00010110_s :=  (if_then_else_M (EQ_M (to x5) (i 4)) qa00020110   (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10010110 (if_then_else_M (EQ_M (to x5) (i 1)) qa00011110  O))).
Definition qa00000111_s :=    (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10000111 (if_then_else_M (EQ_M (to x5) (i 1)) qa00001111  O)).
(************qa00000000 -> qa00000100 ->qa00010100 ->**************************)
(*qa00020100, qa10010100 , qa00011100 , qa00110100, qa00010110***)
Definition qa00020100_s :=    (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa10020100 (if_then_else_M (EQ_M (to x5) (i 1)) qa00021100  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa00120100 (if_then_else_M (EQ_M (to x5) (i 3)) qa00020110  O)))).


Definition  qa00110100_s :=  (if_then_else_M (EQ_M (to x5) (i 3))  qa00210100  (if_then_else_M (EQ_M (to x5) (i 4)) qa00120100  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10110100 (if_then_else_M (EQ_M (to x5) (i 1)) qa00111100  O)))).

(**********************qa00000000 -> qa00000100 -> qa00000101 ->**************************************************************)
(* qa10000101,  qa00001101 ,  qa00100101   qa00000111 *)

Definition   qa00100101_s := (if_then_else_M (EQ_M (to x5) (i 3))  qa00200101  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10100101 (if_then_else_M (EQ_M (to x5) (i 1)) qa00101101 O))).

(*****************///end qa00000100///**********************************************)
(***********************************************************************************)


(*****************///start  qa001000000 ///**********************************************)
(***********************************************************************************)
(************qa00000000 -> qa001000000 -> qa00200000 ->*)
(*qa10200000, qa00201000 , qa01200000, qa00200100,qa00210000, qa00200001*)


Definition  qa00200100_s :=  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10200100 (if_then_else_M (EQ_M (to x5) (i 1)) qa00201100 (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa00210100 (if_then_else_M (EQ_M (to x5) (i 4)) qa00200101 O)))).

Definition qa00210000_s :=  (if_then_else_M (EQ_M (to x5) (i 4)) qa00220000 (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10210000 (if_then_else_M (EQ_M (to x5) (i 1)) qa00211000  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa01210000 (if_then_else_M (EQ_M (to x5) (i 1)) qa00210100 O))))).
Definition  qa00200001_s := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10200001 (if_then_else_M (EQ_M (to x5) (i 1)) qa00201001  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01200001 (if_then_else_M (EQ_M (to x5) (i 2)) qa00200101 O)))).


(************qa00000000 -> qa00100000 -> qa00100100 ->***********************)
(* qa00200100, qa10100100, qa00101100, qa00110100 qa00100101 *)

(************qa00000000 -> qa001000000 -> qa00110000 ->*********************)
(*qa00210000 qa00120000 qa10110000 qa00111000 qa01110000 qa00110100*)

Definition  qa00120000_s :=  (if_then_else_M (EQ_M (to x5) (i 3))  qa00220000  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10120000 (if_then_else_M (EQ_M (to x5) (i 1)) qa00121000  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))  qa01120000 (if_then_else_M (EQ_M (to x5) (i 2)) qa00120100 O))))).

(****************qa00000000 -> qa00100000 -> qa00100001->******************************)
(*qa00200001 qa10100001 qa00101001 qa02100001 qa00100101*)

Definition  qa02100001_s := (if_then_else_M (EQ_M (to x5) (i 3))  qa02200001    (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa12100001 (if_then_else_M (EQ_M (to x5) (i 1)) qa02101001 O))).


(*****************///end  qa00100000 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00000010 ///**********************************************)
(***********************************************************************************)
(*****************qa00000000 -> qa00000010 ->  qa00010010 ->**)
(** qa00020010  qa10010010  qa00011010  qa01010010  qa00010110**)
Definition  qa00020010_s :=    (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa10020010  (if_then_else_M (EQ_M (to x5) (i 1)) ( qa00021010)  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa01020010 (if_then_else_M (EQ_M (to x5) (i 1))  qa00020110 O)))).

(***********qa00000000 -> qa00000010 ->qa00000011->***************************)

(**qa10000011 qa00001011 qa01000011 qa00000111**)

(*****************///end   qa00000010 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00010000 ///**********************************************)
(***********************************************************************************)
(**********qa00000000 -> qa00010000 -> qa00020000 -> ***)
(*qa10020000, qa00021000, qa01020000 , qa00020100 , qa00120000 qa00020010*)


Definition  qa01020000_s  :=  (if_then_else_M (EQ_M (to x5) (i 2))  qa02020000  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa11020000 (if_then_else_M (EQ_M (to x5) (i 1))  qa01021000  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa01120000 (if_then_else_M (EQ_M (to x5) (i 3))  qa01020010 O))))).



(**qa00000000 -> qa00010000 ->qa01010000 ->***)
(**qa02010000 qa01020000 qa11010000 qa01011000 qa01110000 qa01010010*)



(*****************///end  qa00010000 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00000001 ///**********************************************)
(***********************************************************************************)
(**********qa00000000 -> qa00000001 -> qa10000001 ->*)



(***************qa00000000 -> qa00000001 -> qa00001001 ->**********)


(** qa00000000 -> qa00000001 -> qa01000001 ->*)



(*****************///end  qa00000001 ///**********************************************)
(***********************************************************************************)

(**************************************************************************************************)
(**************************************************************************************************)



Definition qa20000000_ss:=    (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa21000000_s  (if_then_else_M (EQ_M (to x5) (i 2)) qa20000100_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa20100000_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa20000010_s (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa20010000_s  (if_then_else_M (EQ_M (to x5) (i 4)) qa20000001_s O)))))).
Definition qa11000000_ss := (if_then_else_M (EQ_M (to x5) (i 1))  qa21000000_s (if_then_else_M (EQ_M (to x5) (i 2)) qa12000000_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa11100000_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa11000010_s (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa11010000_s  (if_then_else_M (EQ_M (to x5) (i 4))  qa20000001_s O)))))).
Definition qa10000100_ss:= (if_then_else_M (EQ_M (to x5) (i 1))  qa20000100_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa10100100_s (if_then_else_M (EQ_M (to x5) (i 3)) qa10000110_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa10010100_s  (if_then_else_M (EQ_M (to x5) (i 4)) qa10000101_s O))))).

Definition qa10100000_ss:= (if_then_else_M (EQ_M (to x5) (i 1))  qa20100000_s  (if_then_else_M (EQ_M (to x5) (i 3))   qa10200000_s (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa11100000_s  (if_then_else_M (EQ_M (to x5) (i 2)) qa10100100_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa10110000_s   (if_then_else_M (EQ_M (to x5) (i 4)) qa10100001_s O)))))).
Definition qa10000010_ss := (if_then_else_M (EQ_M (to x5) (i 1))  qa20000010_s  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa11000010_s  (if_then_else_M (EQ_M (to x5) (i 2))  qa10000110  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))qa10010010_s  (if_then_else_M (EQ_M (to x5) (i 4)) qa10000011_s O))))).

Definition qa10010000_ss:=  (if_then_else_M (EQ_M (to x5) (i 1)) qa20010000_s  (if_then_else_M (EQ_M (to x5) (i 4))   qa10020000_s (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))  qa11010000_s (if_then_else_M (EQ_M (to x5) (i 2))  qa10010100_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa10110000_s (if_then_else_M (EQ_M (to x5) (i 3))  qa10010010_s  O)))))).

Definition qa10000001_ss:= (if_then_else_M (EQ_M (to x5) (i 1)) qa20000001_s   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))  qa11000001_s  (if_then_else_M (EQ_M (to x5) (i 2)) qa10000101_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa10100001_s  (if_then_else_M (EQ_M (to x5) (i 3))  qa10000011_s O))))).


(*******************qa00001000*******************************************************)


Definition qa01001000_ss := (if_then_else_M (EQ_M (to x5) (i 2))  qa02001000_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa01101000_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa01001010_s   (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa01011000_s  (if_then_else_M (EQ_M (to x5) (i 4)) qa01001001_s O))))).

Definition qa00001100_ss := (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00101100_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa00001110_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) (*qa00011100_s*) O (if_then_else_M (EQ_M (to x5) (i 4))  qa00001101_s O)))).

Definition qa00101000_ss := (if_then_else_M (EQ_M (to x5) (i 3))   qa00201000_s   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01101000_s  (if_then_else_M (EQ_M (to x5) (i 2)) 
qa00101100_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa00111000_s (if_then_else_M (EQ_M (to x5) (i 4))  qa00101001_s O))))).


Definition qa00001010_ss :=    (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))
 qa01001010_s  (if_then_else_M (EQ_M (to x5) (i 2)) qa00001110_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa00011010_s  (if_then_else_M (EQ_M (to x5) (i 4))  qa00001011_s O)))).

Definition qa00011000_ss :=  (if_then_else_M (EQ_M (to x5) (i 4)) qa00021000_s   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01011000_s  (if_then_else_M (EQ_M (to x5) (i 2)) (*qa00011100_s*) O  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00111000_s (if_then_else_M (EQ_M (to x5) (i 3))  qa00011010_s O))))).

Definition qa00001001_ss :=  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01001001_s  (if_then_else_M (EQ_M (to x5) (i 2))  qa00001101_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00101001_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa00001011_s O)))).


(**************************qa01000000*******************************************************)




Definition qa02000000_ss := (if_then_else_M (EQ_M (to x5) (i 2)) qa12000000_s   (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa02100000_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa02000010_s (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa02010000_s  (if_then_else_M (EQ_M (to x5) (i 4))  qa02000001_s O))))).


Definition qa01100000_ss  :=    (if_then_else_M (EQ_M (to x5) (i 2))  qa02100000_s  (if_then_else_M (EQ_M (to x5) (i 3))  qa01200000_s  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa11100000_s  (if_then_else_M (EQ_M (to x5) (i 1))  qa01101000_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa01110000_s  (if_then_else_M (EQ_M (to x5) (i 4))  qa01100001_s O)))))).

Definition qa01000010_ss :=  (if_then_else_M (EQ_M (to x5) (i 2))  qa02000010_s   (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa11000010_s  (if_then_else_M (EQ_M (to x5) (i 1))  qa01001010_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa01010010_s  (if_then_else_M (EQ_M (to x5) (i 4)) qa01000011_s O))))).

Definition qa01010000_ss := (if_then_else_M (EQ_M (to x5) (i 2))  qa02010000_s  (if_then_else_M (EQ_M (to x5) (i 4))  qa01020000_s  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa11010000_s  (if_then_else_M (EQ_M (to x5) (i 1)) qa01011000_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa01110000_s (if_then_else_M (EQ_M (to x5) (i 3)) qa01010010_s O)))))).

Definition qa01000001_ss:=  (if_then_else_M (EQ_M (to x5) (i 2))   qa02000001_s  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa11000001_s (if_then_else_M (EQ_M (to x5) (i 1)) qa01001001_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa01100001_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa01000011_s O))))).


(**************************qa00000100*******************************************************)





Definition qa00000110_ss :=    (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa10000110_s  (if_then_else_M (EQ_M (to x5) (i 1))  qa00001110_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa00010110_s  (if_then_else_M (EQ_M (to x5) (i 4))  qa00000111_s O)))).

Definition qa00010100_ss:=  (if_then_else_M (EQ_M (to x5) (i 4)) qa00020100_s    (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10010100_s  (if_then_else_M (EQ_M (to x5) (i 1)) (*qa00011100_s *) O  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa00110100_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa00010110_s O))))).

Definition qa00000101_ss :=  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10000101_s  (if_then_else_M (EQ_M (to x5) (i 1))  qa00001101_s  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00100101_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa00000111_s O)))).


(**************************qa001000000*******************************************************)

Definition qa00200000_ss := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10200000_s  (if_then_else_M (EQ_M (to x5) (i 1)) qa00201000_s (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01200000_s (if_then_else_M (EQ_M (to x5) (i 2)) qa00200100_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa00210000_s  (if_then_else_M (EQ_M (to x5) (i 4)) qa00200001_s O)))))).


Definition qa00100100_ss :=  (if_then_else_M (EQ_M (to x5) (i 3))  qa00200100_s  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10100100_s  (if_then_else_M (EQ_M (to x5) (i 1))  qa00101100_s  (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa00110100_s  (if_then_else_M (EQ_M (to x5) (i 4))  qa00100101_s O))))).

Definition qa00110000_ss := (if_then_else_M (EQ_M (to x5) (i 3))  qa00210000_s  (if_then_else_M (EQ_M (to x5) (i 4)) qa00120000_s    (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10110000_s  (if_then_else_M (EQ_M (to x5) (i 1))  qa00111000_s  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01110000_s  (if_then_else_M (EQ_M (to x5) (i 2)) qa00110100_s O)))))).

Definition qa00100001_ss := (if_then_else_M (EQ_M (to x5) (i 3)) qa00200001_s   (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10100001_s  (if_then_else_M (EQ_M (to x5) (i 1)) qa00101001_s  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa02100001_s  (if_then_else_M (EQ_M (to x5) (i 2)) qa00100101_s O))))).

(**************************qa00000010*******************************************************)



Definition qa00010010_ss:=  (if_then_else_M (EQ_M (to x5) (i 4))  qa00020010_s   (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa10010010_s  (if_then_else_M (EQ_M (to x5) (i 1))  qa00011010_s  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))  qa01010010_s (if_then_else_M (EQ_M (to x5) (i 2))  qa00010110_s O))))).

Definition qa00000011_ss :=  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa10000011  (if_then_else_M (EQ_M (to x5) (i 2))  qa00001011  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa01000011  (if_then_else_M (EQ_M (to x5) (i 3))  qa00000111 O)))).

(**************************qa00010000*******************************************************)




Definition qa00020000_ss := (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10020000_s (if_then_else_M (EQ_M (to x5) (i 1))  qa00021000_s  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01020000_s  (if_then_else_M (EQ_M (to x5) (i 2)) qa00020100_s     (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00120000_s  (if_then_else_M (EQ_M (to x5) (i 3)) qa00020010_s O)))))) .




(**************************qa00000001*******************************************************)










Definition qa10000000_sss :=  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (reveal x5) (i 3) ) O (if_then_else_M (EQ_M (reveal x5) (i 4) ) O (if_then_else_M (EQ_M (to x5) (i 1)) qa20000000_ss  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa11000000_ss  (if_then_else_M (EQ_M (to x5) (i 2)) qa10000100_ss (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa10100000_ss (if_then_else_M (EQ_M (to x5) (i 3)) qa10000010_ss (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa10010000_ss (if_then_else_M (EQ_M (to x5) (i 4)) qa10000001_ss O))))))))))).

Definition qa00001000_sss :=  (if_then_else_M (EQ_M (reveal x5) (i 1) ) & (EQ_M (to x5) (i 1)) mx1rn2 (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (reveal x5) (i 3) ) O (if_then_else_M (EQ_M (reveal x5) (i 4) ) O (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01001000_ss  (if_then_else_M (EQ_M (to x5) (i 2)) qa00001100_ss (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new))  qa00101000_ss  (if_then_else_M (EQ_M (to x5) (i 3))  qa00001010_ss (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa00011000_ss  (if_then_else_M (EQ_M (to x5) (i 4)) qa00001001_ss O)))))))))).


Definition qa01000000_sss :=  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (reveal x5) (i 3) ) O (if_then_else_M (EQ_M (reveal x5) (i 4) ) O (if_then_else_M (EQ_M (to x5) (i 2)) qa02000000_ss (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new))  qa11000000_ss  (if_then_else_M (EQ_M (to x5) (i 1))  qa01001000_ss  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa01100000_ss  (if_then_else_M (EQ_M (to x5) (i 3)) qa01000010_ss (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa01010000_ss  (if_then_else_M (EQ_M (to x5) (i 4)) qa01000001_ss O))))))))))).

 Definition qa0000100_sss :=  (if_then_else_M (EQ_M (reveal x5) (i 2) ) & (EQ_M (to x5) (i 2)) mx1rn2 (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (reveal x5) (i 3) ) O (if_then_else_M (EQ_M (reveal x5) (i 4) ) O  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01001000_ss  (if_then_else_M (EQ_M (to x5) (i 2))  qa00001100_ss (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00101000_ss  (if_then_else_M (EQ_M (to x5) (i 3))  qa00001010_ss (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))   qa00011000_ss (if_then_else_M (EQ_M (to x5) (i 4))  qa00001001_ss O)))))))))).

 Definition qa00100000_sss :=  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (reveal x5) (i 3) ) O (if_then_else_M (EQ_M (reveal x5) (i 4) ) O  (if_then_else_M (EQ_M (to x5) (i 3)) qa02000000_ss (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa11000000_ss (if_then_else_M (EQ_M (to x5) (i 1))  qa01001000_ss (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01100000_ss  (if_then_else_M (EQ_M (to x5) (i 2)) qa01000010_ss (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa01010000_ss  (if_then_else_M (EQ_M (to x5) (i 4)) qa01000001_ss O))))))))))).

Definition  qa00000010_sss  :=   (if_then_else_M (EQ_M (reveal x5) (i 3) ) & (EQ_M (to x5) (i 3)) mx1rn2 (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (reveal x5) (i 4) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10000100_ss (if_then_else_M (EQ_M (to x5) (i 4)) qa00001100_ss   (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa00101000_ss  (if_then_else_M (EQ_M (to x5) (i 2))  qa00000110_ss (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new))  qa00010100_ss  (if_then_else_M (EQ_M (to x5) (i 4)) qa00000101_ss O)))))))))).

Definition  qa00010000_sss  :=    (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (reveal x5) (i 3) ) O (if_then_else_M (EQ_M (reveal x5) (i 4) ) O  (if_then_else_M (EQ_M (to x5) (i 4)) qa00200000_ss  (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10100000_ss  (if_then_else_M (EQ_M (to x5) (i 1)) qa00101000_ss  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new))  qa01100000_ss  (if_then_else_M (EQ_M (to x5) (i 2))   qa00100100_ss (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00110000_ss  (if_then_else_M (EQ_M (to x5) (i 3))  qa00100001_ss O))))))))))).
Definition  qa00000001_sss := (if_then_else_M (EQ_M (reveal x5) (i 4) ) & (EQ_M (to x5) (i 4)) mx1rn2 (if_then_else_M (EQ_M (reveal x5) (i 1) ) O  (if_then_else_M (EQ_M (reveal x5) (i 2) ) O   (if_then_else_M (EQ_M (reveal x5) (i 3) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10000001_ss  (if_then_else_M (EQ_M (to x5) (i 1)) qa00001001_ss (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01000001_ss  (if_then_else_M (EQ_M (to x5) (i 2)) qa00000101_ss  (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00100001_ss  (if_then_else_M (EQ_M (to x5) (i 3)) qa00000011_ss O)))))))))).



(********************************************************************)


Definition t16 :=  msg  (if_then_else_M (EQ_M (reveal x5) (i 1) ) O (if_then_else_M (EQ_M (reveal x5) (i 2) ) O  (if_then_else_M (EQ_M (reveal x5) (i 3) ) O (if_then_else_M (EQ_M (reveal x5) (i 4) ) O (if_then_else_M ((EQ_M (to x5) (i 1)) & (EQ_M (act x5) new)) qa10000000_sss  (if_then_else_M (EQ_M (to x5) (i 1)) qa00001000_sss  (if_then_else_M ((EQ_M (to x5) (i 2)) & (EQ_M (act x5) new)) qa01000000_sss (if_then_else_M (EQ_M (to x5) (i 2)) qa00001000_sss (if_then_else_M ((EQ_M (to x5) (i 3)) & (EQ_M (act x5) new)) qa00100000_ss  (if_then_else_M (EQ_M (to x5) (i 3))  qa00000010_sss (if_then_else_M ((EQ_M (to x5) (i 4)) & (EQ_M (act x5) new)) qa00010000_sss  (if_then_else_M (EQ_M (to x5) (i 4))  qa00000001_sss O)) ))) ) )))))).


Definition phi5:= phi4 ++ [t16]. 


(**************************************phi6*********************************************************)
(***********************************************************************************************)

(*
Definition mx3rn1 := (exp (G 0) (m x5) (r 1)).
Definition mx3rn2 := (exp (G 0) (m x3) (r 2)).
Definition mx3rn3 := (exp (G 0) (m x3) (r 3)).*)
Definition mphi5 := (conv_mylist_listm phi5).
Definition x6 := (f mphi5).


(************/// start qa10000000/// ***************)

(********************************start qa20000000******************************)
(***/// qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ///***)
(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> qa22000000 -> *********)
(** qa22100000  qa22000010  qa22010000  qa22000001   *)
Definition qa22100000  := (if_then_else_M (EQ_M (to x6) (i 3))  acc   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 276) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 276) O) )).
Definition  qa22000010 := (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 277) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 277) O) ).
Definition  qa22010000 := (if_then_else_M (EQ_M (to x6) (i 4))  acc  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 278) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 278) O) )).
Definition  qa22000001 :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 279) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 279) O) ).


(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21100000 -> *********)
(*
Definition qa22100000 := (if_then_else_M (EQ_M (to x6) (i 3))  acc    (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 167) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 167) O) )).
*)
Definition qa21200000 :=(if_then_else_M (EQ_M (to x6) (i 2))  acc    (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 280) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 280) O) )).
 Definition qa21110000 := (if_then_else_M (EQ_M (to x6) (i 2))  acc   (if_then_else_M (EQ_M (to x6) (i 3))  acc   (if_then_else_M (EQ_M (to x6) (i 4))  acc  O))).
Definition qa21100001 :=  (if_then_else_M (EQ_M (to x6) (i 2))  acc  (if_then_else_M (EQ_M (to x6) (i 2))  acc  O)).

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21000010  -> *********)
(*
Definition qa22000010  := (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 281) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 281) O) ). *)
Definition qa21010010  := (if_then_else_M (EQ_M (to x6) (i 2))  acc  (if_then_else_M (EQ_M (to x6) (i 4))  acc O)).
Definition qa21000011  :=  (if_then_else_M (EQ_M (to x6) (i 2))  acc O).

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21010000  -> *********)
(*Definition  qa22010000 := O.*)
Definition qa21020000 := (if_then_else_M (EQ_M (to x6) (i 2))  acc    (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 281) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 281) O) )).
(*Definition qa21110000 := O.
Definition  qa21010010 :=O *)

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21000001  -> *********)
(*
Definition qa22000001 := O. 
Definition qa21100001 := O.
Definition qa21000011 := O.*)

(*********/// qa00000000 -> qa10000000 -> qa20000000 ->  qa20000100 ->///*************)

(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20100100->*****************************************)
Definition  qa20200100 :=  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 282) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 282) O) ).
Definition qa20110100 := (if_then_else_M (EQ_M (to x6) (i 3))  acc  (if_then_else_M (EQ_M (to x6) (i 4))  acc  O)).
Definition  qa20100101 := (if_then_else_M (EQ_M (to x6) (i 3))  acc O).

(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20000110->**********)

Definition qa20010110 := (if_then_else_M (EQ_M (to x6) (i 4)) acc O).
Definition qa20000111 := O.

(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20010100 ->**********)
Definition qa20020100 := (if_then_else_M (EQ_M (to x6) (i 4)) acc O).

 (*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->   qa20000101 ->**********)

(****///qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->///*************)

 (****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20200000->*************)



Definition qa20210000 := (if_then_else_M (EQ_M (to x6) (i 4)) acc O).



 (****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20110000->*************)
(*Definition qa20210000 := O.*)
Definition qa20120000 := (if_then_else_M (EQ_M (to x6) (i 3)) acc O).

(****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20100001->*************)

Definition qa20200001 :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) (grn 283) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 283) O) ).

(************************///qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 ->///**********)
(**************************qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 -> qa20010010 ->************* *************)
Definition qa20020010 := (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) (grn 284) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 284) O) ).



(*******qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 -> qa20000011->*************)



(*********************///qa00000000 -> qa10000000 -> qa20000000 ->qa20010000->///*****)
(*******************qa00000000 -> qa10000000 -> qa20000000 ->qa20010000->qa20020000->**)


(***********************end  qa20000000********************************)


(*************************start  qa11000000 **************************)

(******** /// qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 /// -> *)
(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 -> qa12100000 ->  *)

(*Definition qa22100000 :=  O.*)
Definition qa12200000 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 284) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 284) O) ) ).

Definition qa12110000 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 3)) acc (if_then_else_M (EQ_M (to x6) (i 4)) acc O))).


(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->  qa12000010 ->  *)

(*Definition qa22000010 := (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 284) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 284) O) ). *)
Definition qa12010010 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 4)) acc O)).
Definition qa12000011 :=   (if_then_else_M (EQ_M (to x6) (i 1)) acc O).

(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->  qa12010000 ->  *)


Definition qa12020000 := (if_then_else_M (EQ_M (to x6) (i 1)) acc  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 285) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 285) O) )).


(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->   qa12000001 ->  *)

(***///qa00000000 -> qa10000000 -> qa11000000 ->qa11100000->///******************)
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000-> qa11200000->******************)


Definition qa11210000  := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 2)) acc (if_then_else_M (EQ_M (to x6) (i 4)) acc O))).
Definition qa11200001 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 2)) acc O)).

(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000-> qa11110000->******************)


Definition qa11120000 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 2)) acc (if_then_else_M (EQ_M (to x6) (i 3)) acc O))).
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000->qa11100001->******************)

(*************///qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 ->/// ****************)
(*************qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 -> qa11010010-> ****************)

Definition qa11020010 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 2)) acc O))  .


(*************qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 ->qa11000011 -> ****************)

 (**************///qa00000000 -> qa10000000 -> qa11000000 ->qa11010000->/// ***********)

(**************qa00000000 -> qa10000000 -> qa11000000 ->qa11010000-> qa11020000 -> ***********)

(**************qa00000000 -> qa10000000 -> qa11000000 ->qa11010000-> qa11110000 -> ***********)

(**************qa00000000 -> qa10000000 -> qa11000000 ->qa11010000->  qa11010010 -> ***********)




(*****************end qa11000000 **********************************************)

(****************start qa10000100 ********************************************)
(********/// qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->///  *)
(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->  qa10200100-> *)

Definition  qa10210100 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 4)) acc O)).
Definition   qa10200101 :=  (if_then_else_M (EQ_M (to x6) (i 1)) acc O).
(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->   qa10110100-> *)
Definition qa2011010 :=  (if_then_else_M (EQ_M (to x6) (i 3)) acc (if_then_else_M (EQ_M (to x6) (i 4)) acc O)).
(*Definition qa10210100 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 4)) acc O)).*)
Definition  qa10120100 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 3)) acc O)).

(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->   qa10100101-> *)

(*************** /// qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 ->///*********)
(***************  qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 -> qa10010110 -> *********)


(*Definition qa20010110  := O.*)
Definition qa10020110  :=   (if_then_else_M (EQ_M (to x6) (i 1)) acc O).
(***************  qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 -> qa10000111  -> *********)

(*Definition qa20000111  := O. *)
(******************************/// qa00000000 ->  qa10000000 -> qa10000100 -> qa10010100->///************)
(****************************** qa00000000 ->  qa10000000 -> qa10000100 -> qa10010100-> qa10020100 ->*************************)




(******************end   qa10000100 ***********************)

(*****************************start qa10100000 **********)

(******** ///qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 ->///   *)
(******** qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 -> qa10210000->  *)

(*Definition qa20210000 := O.*)
Definition qa10220000 := (if_then_else_M (EQ_M (to x6) (i 1)) acc O).

(******** qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 -> qa10200001->  *)

(******************///qa00000000 -> qa10000000 -> qa10100000 -> qa10110000->///*)
(******************qa00000000 -> qa10000000 -> qa10100000 -> qa10110000->  qa10120000 ->*)





(*****************************end qa10100000 **********)


(*****************************start qa10000010 **********)
(********/// qa00000000 -> qa10000000 -> qa10000010 -> qa10010010 ->///  *)

(******** qa00000000 -> qa10000000 -> qa10000010 -> qa10010010 -> qa10020010  ->  *)









(*****************************end qa10000010 **********)

(*****************************start qa10010000 **********)



(*****************************end qa10010000 **********)


(*****************************start qa10000001 **********)




(********************end qa10000001 **********************************)


(************/// end qa10000000/// ***************)

(**********************************************************************************************)

(************/// start qa00001000/// ***************)

(****************************start qa01001000 **********)
(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 ->/// *)
(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> qa02101000 -> *)
 
Definition qa02201000 :=   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 236) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 236) O) ).
Definition qa02111000 :=  (if_then_else_M (EQ_M (to x6) (i 3)) acc  (if_then_else_M (EQ_M (to x6) (i 1)) acc O)).
(*Definition qa02101001 :=  (if_then_else_M (EQ_M (to x6) (i 3)) acc O).*)
(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 ->  qa02001010 -> *)
Definition qa02011010 := (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 237) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 237) O) ).
Definition  qa02001011 := O.

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 ->  qa02011000-> *)
Definition qa02021000 := (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 237) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 237) O) ).

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> qa02001001  -> *)

(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->/// *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->  qa01201000 -> *)


Definition  qa01211000 :=    (if_then_else_M (EQ_M (to x6) (i 2)) acc  (if_then_else_M (EQ_M (to x6) (i 4)) acc O)).

Definition  qa01201001 :=  (if_then_else_M (EQ_M (to x6) (i 1)) acc O).

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->  qa01111000  -> *)

Definition qa01121000 :=  (if_then_else_M (EQ_M (to x6) (i 2)) acc (if_then_else_M (EQ_M (to x6) (i 3)) acc O)).

(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 ->/// *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 ->  qa01011010 -> *)

  (*Definition qa02011010:= (if_then_else_M (EQ_M (to x6) (i 2)) acc O).*)
Definition qa01021010 := (if_then_else_M (EQ_M (to x6) (i 2)) acc O).


(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01011000 ->/// *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01011000 -> qa01021000 -> *)


(***///qa00000000 -> qa00001000 ->  qa01001000 ->   qa01001001->/// *)
(***qa00000000 -> qa00001000 ->  qa01001000 ->   qa01001001-> *)

(****************************end qa01001000 **********)

(*************************start qa00001100 ************)
(***///qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> /// *)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> qa00201100 -> *)
Definition qa00211100 := (if_then_else_M (EQ_M (to x6) (i 4)) acc O).
Definition qa00201101 :=  O.
 
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 ->   qa00111100  -> *)
(*Definition  qa00211100 := O.*)
Definition  qa00121100 := (if_then_else_M (EQ_M (to x6) (i 3)) acc O).

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> qa00101101   -> *)
(*Definition qa00201101 := O.*)
(**///*qa00000000 -> qa00001000 ->  qa00001100 -> qa00001110 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001110 -> qa00011110 -> *)

Definition qa00021110 := O.

 
(***///qa00000000 -> qa00001000 ->  qa00001100 -> qa00011100 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00011100 -> qa00021100 -> *)

(*Definition qa00121100 := O.*)
(*Definition qa00021110 :=  O.*)
(***///qa00000000 -> qa00001000 ->  qa00001100 -> qa00001101 ->/// *)

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001101 -> *)
(*Definition qa00101101 := O.
Definition qa00001111 := O.*)

(************** end qa00001100 ************)
(*************************start  qa00101000 ************)
(***///qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 ->qa00211000 -> *)
Definition qa00221000 :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) (grn 238) (if_then_else_M (EQ_M (to x6) (i 2)) (grn 238) O)).

(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 -> qa00201001 -> *)


(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 -> qa00201001 -> *)



(***///qa00000000 -> qa00001000 ->  qa00101000 -> qa00111000 -> ///*)

(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00111000 ->qa00121000 -> *)



(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00101001 -> *)

(*************************end  qa00101000 ********)
(*********************start qa00001010 ************)

(***///qa00000000 -> qa00001000 ->  qa00001010 ->  qa00011010 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001010 ->  qa00011010 ->  qa00021010 -> *)


 


(***********end qa00001010 ************)
(***********************start qa00011000 ****)


(***********************end qa00011000 ****)
(*********commented out qa00001001**********)

(************/// end qa00001000/// ***************)

(************/// start qa01000000/// ***************)

(******* start qa02000000 ************)
(***///qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> ///*)
(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> qa02200000 -> *)


Definition qa02210000 :=  (if_then_else_M (EQ_M (to x6) (i 4)) acc  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) (grn 239) (if_then_else_M (EQ_M (to x6) (i 1)) (grn 239) O))).


(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 ->  qa02110000 -> *)

Definition qa02120000 :=  (if_then_else_M (EQ_M (to x6) (i 3)) acc  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) (grn 240) (if_then_else_M (EQ_M (to x6) (i 1)) (grn 240) O))).


(***///qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 ->/// *)
(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 -> qa02010010 -> *)

Definition qa02020010 :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) (grn 241) (if_then_else_M (EQ_M (to x6) (i 1)) (grn 241) O)).

(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 ->  qa02000011 -> *)


(***///qa00000000 ->  qa01000000 ->  qa02000000 ->qa02010000 -> ///*)
(***qa00000000 ->  qa01000000 ->  qa02000000 ->qa02010000 -> qa02020000 -> *)


(******* end qa02000000 ************)
(******* start qa01100000 ************)
(*///qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->///*)
(*qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->qa01210000 -> *)

Definition qa01220000 :=  (if_then_else_M (EQ_M (to x6) (i 2)) acc (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) (grn 242) (if_then_else_M (EQ_M (to x6) (i 1)) (grn 242) O))).

(*qa00000000 -> qa01000000 -> qa01100000 -> qa01200000-> qa01200001 -> *)


(*///qa00000000 -> qa01000000 -> qa01100000 ->  qa01110000 ->///*)
(*qa00000000 -> qa01000000 -> qa01100000 ->  qa01110000 -> qa01120000 ->*)



(******* end qa01100000 ************)
(******* start qa01000010************)
(*///qa00000000 -> qa01000000 ->qa01000010 -> qa01010010 ->/// **)
(*qa00000000 -> qa01000000 ->qa01000010 -> qa01010010 -> qa01020010 -> **)




(******* end qa01000010************)

(**********qa01000001 commented out***********)
(************/// end qa01000000/// ***************)
(************/// start qa00000100/// ***************)
(*******start qa00000110************)
(*///qa00000000 -> qa00000100 ->  qa00000110 -> qa00010110 ->/// **)
(*qa00000000 -> qa00000100 ->  qa00000110 -> qa00010110 -> qa00020110 -> **)





(*******end qa00000110************)
(*********start qa00010100 ****************************)
(*///qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 ->/// **)
(*qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 -> qa00120100 -> **)

Definition qa00220100 :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) (grn 243) (if_then_else_M (EQ_M (to x6) (i 1)) (grn 243) O)).



(*********end qa00010100 ****************************)
(********start qa00000101 **************************)
(*///qa00000000 -> qa00000100 ->  qa00000101-> qa00100101 ->/// **)
(*qa00000000 -> qa00000100 ->  qa00000101-> qa00100101 -> qa00200101 -> **)


(********end qa00000101 **************************)


(************/// end qa00000100/// ***************)

(************/// start qa00100000/// ***************)
(******* start qa00200000************)



(*///qa00000000 ->  qa00100000  -> qa00200000 -> qa00210000 -> ///**)
(*qa00000000 ->  qa00100000  -> qa00200000 -> qa00210000 -> qa00220000 -> **)


(*****start qa00100001**********************)



(*****end qa00100001**********************)

(************/// end qa00000010/// ***************)


(************/// start qa00010000/// ***************)
(**********************start qa00020000 ****************)


(**********************stop qa00020000 ****************)
(************/// end qa00010000/// ***************)


(************/// start qa00000001/// ***************)
(*********start  qa10000001  ***********************)
(*qa00000000 ->  qa00000001 -> qa10000001 ->  qa10100001  ->*)


(********end qa10000001 ***************************)
(************/// end qa00000001/// ***************)
(*****************_s ing*******************************)

(************/// start qa10000000/// ***************)

(********************************start qa20000000******************************)

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> *********)
(** qa22000000  qa21100000  qa21000010  qa21010000 qa21000001 *)

Definition qa22000000_s :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa22100000 (if_then_else_M (EQ_M (to x6) (i 3)) qa22000010  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa22010000 (if_then_else_M (EQ_M (to x6) (i 4)) qa22000001 O) ))).


Definition qa21100000_s := (if_then_else_M (EQ_M (to x6) (i 2))  qa22100000 (if_then_else_M (EQ_M (to x6) (i 3))  qa21200000  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa21110000 (if_then_else_M (EQ_M (to x6) (i 4)) qa21100001 O) ))).

Definition   qa21000010_s := (if_then_else_M (EQ_M (to x6) (i 2))  qa22000010   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa21010010 (if_then_else_M (EQ_M (to x6) (i 4)) qa21000011 O) )).

Definition  qa21010000_s :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa22010000  (if_then_else_M (EQ_M (to x6) (i 3)) qa21020000   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa21110000 (if_then_else_M (EQ_M (to x6) (i 3)) qa21010010 O) ))).

Definition  qa21000001_s := (if_then_else_M (EQ_M (to x6) (i 2)) qa22000001   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa21100001 (if_then_else_M (EQ_M (to x6) (i 3)) qa21000011 O) )).


(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->*****************************************)
(** qa20100100  qa20000110  qa20010100  qa20000101*)

Definition qa20100100_s  :=  (if_then_else_M (EQ_M (to x6) (i 3))   qa20200100    (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa20110100 (if_then_else_M (EQ_M (to x6) (i 4)) qa20100101 O) )).

Definition  qa20000110_s :=     (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa20010110 (if_then_else_M (EQ_M (to x6) (i 4)) qa20000111 O) ).
Definition  qa20010100_s  :=   (if_then_else_M (EQ_M (to x6) (i 4))  qa20020100 (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa20110100 (if_then_else_M (EQ_M (to x6) (i 3)) qa20010110 O) )).
Definition  qa20000101_s :=      (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20100101 (if_then_else_M (EQ_M (to x6) (i 3)) qa20000111 O) ).

(****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->*************)
(**qa20200000 qa21100000 qa20100100  qa20110000 qa20100001*)
Definition qa20200000_s :=(if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21200000 (if_then_else_M (EQ_M (to x6) (i 2))  qa20200100 (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa20210000 (if_then_else_M (EQ_M (to x6) (i 4))  qa20200001 O) ))).

Definition   qa20110000_s :=(if_then_else_M (EQ_M (to x6) (i 3))  qa20210000 (if_then_else_M (EQ_M (to x6) (i 4)) qa20120000 (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21110000 (if_then_else_M (EQ_M (to x6) (i 2)) qa20110100 O) ))).

Definition  qa20100001_s := (if_then_else_M (EQ_M (to x6) (i 3))  qa20200001 (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21100001 (if_then_else_M (EQ_M (to x6) (i 2))  qa20100101 O) )).

(************************qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 ->*************)
(***qa21000010 qa20000110 qa20010010 qa20000011****************************************************)

Definition  qa20010010_s := (if_then_else_M (EQ_M (to x6) (i 4)) qa20020010 (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21010010 (if_then_else_M (EQ_M (to x6) (i 2)) qa20010110 O) )).
Definition  qa20000011_s :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21000011 (if_then_else_M (EQ_M (to x6) (i 2)) qa20000111 O) ).

(*******************qa00000000 -> qa10000000 -> qa20000000 ->qa20010000->******************)
(**qa20020000 qa21010000 qa20010100 qa20110000 qa20010010 **************)
Definition qa20020000_s :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21020000 (if_then_else_M (EQ_M (to x6) (i 2)) qa20020100 (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20120000 (if_then_else_M (EQ_M (to x6) (i 3)) qa20020010 O) )) ).



(**************qa00000000 -> qa10000000 -> qa20000000 -> qa20000001-> ***************************************)
(**  qa21000001  qa20000101  qa20100001  qa20000011*********)


(***********************end  qa20000000********************************)


(*************************start  qa11000000 **************************)

(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 -> *)


Definition  qa12100000_s :=
 (if_then_else_M (EQ_M (to x6) (i 1))   qa22100000 (if_then_else_M (EQ_M (to x6) (i 3))  qa12200000   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa12110000 (if_then_else_M (EQ_M (to x6) (i 4))  qa12100001 O) )) ).
Definition  qa12000010_s :=    (if_then_else_M (EQ_M (to x6) (i 1))  qa22000010  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa12010010 (if_then_else_M (EQ_M (to x6) (i 4)) qa12000011 O) )) .
Definition  qa12010000_s :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa22010000 (if_then_else_M (EQ_M (to x6) (i 4))  qa12020000  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa12110000 (if_then_else_M (EQ_M (to x6) (i 3)) qa12010010 O) )) ).
Definition  qa12000001_s :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa22000001 (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa12100001 (if_then_else_M (EQ_M (to x6) (i 4)) qa12000011 O) ) ).
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000->******************)


Definition  qa11200000_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa21200000 (if_then_else_M (EQ_M (to x6) (i 2)) qa12200000  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa11210000 (if_then_else_M (EQ_M (to x6) (i 4))  qa11200001 O) )) ).
Definition  qa11110000_s :=(if_then_else_M (EQ_M (to x6) (i 1)) qa21110000 (if_then_else_M (EQ_M (to x6) (i 2)) qa12110000  (if_then_else_M (EQ_M (to x6) (i 3)) qa11210000 (if_then_else_M (EQ_M (to x6) (i 4))  qa11120000  O) )) ).
Definition  qa11100001_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa21100001 (if_then_else_M (EQ_M (to x6) (i 2)) qa12100001  (if_then_else_M (EQ_M (to x6) (i 3))  qa11200001 O ))).
(*************qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 -> ****************)

Definition   qa11010010_s := (if_then_else_M (EQ_M (to x6) (i 1))  qa21010010 (if_then_else_M (EQ_M (to x6) (i 2)) qa12010010 (if_then_else_M (EQ_M (to x6) (i 4)) qa11020010   O) ) ).

Definition   qa11000011_s :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa21000011 (if_then_else_M (EQ_M (to x6) (i 2)) qa12000011    O) ).

(**************qa00000000 -> qa10000000 -> qa11000000 ->qa11010000-> ***********)

Definition  qa11020000_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa21020000 (if_then_else_M (EQ_M (to x6) (i 2)) qa12020000  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa11120000 (if_then_else_M (EQ_M (to x6) (i 3)) qa11020010 O ) ))).

(****************************************qa00000000 -> qa10000000 -> qa11000000 -> qa11000001-> *)
(****qa21000001 qa12000001 qa11100001 qa11000011 *)


(*****************end qa11000000 **********************************************)

(****************start qa10000100 ********************************************)

(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->  *)
(**  qa20100100  qa10200100   qa10110100  qa10100101 *)

Definition   qa10200100_s :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa20200100  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10210100 (if_then_else_M (EQ_M (to x6) (i 4)) qa10200101 O) ) ).
Definition    qa10110100_s :=   (if_then_else_M (EQ_M (to x6) (i 1)) qa2011010 (if_then_else_M (EQ_M (to x6) (i 3)) qa10210100   (if_then_else_M (EQ_M (to x6) (i 4)) qa10120100   O) ) ).
Definition  qa10100101_s :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa20100101 (if_then_else_M (EQ_M (to x6) (i 3)) qa10200101   O) ).



(***************  qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 ->*********)


Definition  qa10010110_s  := (if_then_else_M (EQ_M (to x6) (i 1)) qa20010110 (if_then_else_M (EQ_M (to x6) (i 4)) qa10020110   O) ).
Definition  qa10000111_s  := (if_then_else_M (EQ_M (to x6) (i 1)) qa20000111  O) .
(****************************** qa00000000 ->  qa10000000 -> qa10000100 -> qa10010100->*************************)

Definition  qa10020100_s :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa20020100  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa10120100 (if_then_else_M (EQ_M (to x6) (i 3)) qa10020110 O) ) ).


(*** qa00000000 ->  qa10000000 -> qa10000100 ->qa10000101->*****)



(******************end   qa10000100 ***********************)

(*****************************start qa10100000 **********)


(******** qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 ->   *)

(**  qa20200000 qa11200000 qa10200100 qa10210000 qa10200001 *)

Definition  qa10210000_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa20210000  (if_then_else_M (EQ_M (to x6) (i 4)) qa10220000   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11210000 (if_then_else_M (EQ_M (to x6) (i 2))  qa10210100 O) ) )).
Definition  qa10200001_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa20200001   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11200001 (if_then_else_M (EQ_M (to x6) (i 2)) qa10200101 O) ) ).

(******************qa00000000 -> qa10000000 -> qa10100000 -> qa10110000->*)
(*  qa20110000  qa10210000  qa10120000  qa11110000  qa10110100*)

Definition   qa10120000_s := (if_then_else_M (EQ_M (to x6) (i 1))  qa20120000 (if_then_else_M (EQ_M (to x6) (i 3))  qa10220000   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11120000 (if_then_else_M (EQ_M (to x6) (i 2))  qa10120100 O) ) )).

(***qa00000000 -> qa10000000 -> qa10100000 ->qa10100001->***)

(***qa20100001 qa10200001 qa11100001 qa10100101 *)

(*****************************end qa10100000 **********)


(*****************************start qa10000010 **********)

(******** qa00000000 -> qa10000000 -> qa10000010 -> qa10010010 ->  *)


(** qa20010010 qa10020010 qa11010010 qa10010110 *)

(*Definition  qa20010010  := O. *)
Definition  qa10020010_s :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa20020010  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11020010 (if_then_else_M (EQ_M (to x6) (i 2))  qa10020110 O) ) ).


(******* qa00000000 -> qa10000000 -> qa10000010 ->qa1000001->1***)
(**qa20000011 qa11000011 qa10000111 *)


(*****************************end qa10000010 **********)

(*****************************start qa10010000 **********)

(******** qa00000000 ->  qa10000000 -> qa10010000 -> qa20010000 -> ***)
(** qa20020000  qa21010000  qa20010100  qa20110000 qa20010010  *)



(******** qa00000000 ->  qa10000000 -> qa10010000 -> qa10020000 -> ***)
(** qa20020000  qa11020000  qa10020100  qa10120010  *)



(************qa00000000 ->  qa10000000 -> qa10010000 -> qa11010000 -> *)
(*** qa21010000 qa12010000 qa11020000 qa11110000 qa11010010*)



(************qa00000000 ->  qa10000000 -> qa10010000 -> qa10010100 -> *)
(*qa20010100 qa10020100 qa10110100 qa10010110*)

(************qa00000000 ->  qa10000000 -> qa10010000 -> qa10110000 -> *)
(* qa20110000  qa10210000  qa10120000  qa11110000  qa10110100 *)


(************qa00000000 ->  qa10000000 -> qa10010000 -> qa10010010 -> *)
(*qa20010010 qa10020010 qa11010010 qa10010110 *)



(*****************************end qa10010000 **********)


(*****************************start qa10000001 **********)


(********qa00000000 -> qa10000000 -> qa10000001 -> qa20000001 -> **********)
(**qa21000001 qa20000101 qa20100001 qa20000011  *)

(********qa00000000 -> qa10000000 -> qa10000001 -> qa11000001 -> **********)
(** qa21000001  qa12000001  qa11100001  qa11000011   *)

(********qa00000000 -> qa10000000 -> qa10000001 -> qa10000101 -> **********)
(** qa20000101 qa10100101 qa10000111   *)



(********qa00000000 -> qa10000000 -> qa10000001 -> qa10100001 -> **********)

(**qa20100001  qa10200001 qa11100001 qa10100101**)


(********qa00000000 -> qa10000000 -> qa10000001 -> qa10000011 -> **********)
(***qa20000011 qa11000011 qa10000111 *)




(********************end qa10000001 **********************************)


(************/// end qa10000000/// ***************)

(**********************************************************************************************)

(************/// start qa00001000/// ***************)

(****************************start qa01001000 **********)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> *)
 
Definition qa02101000_s :=   (if_then_else_M (EQ_M (to x6) (i 3))  qa02201000  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02111000 (if_then_else_M (EQ_M (to x6) (i 4)) qa02101001 O) ) ).
Definition  qa02001010_s :=     (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02011010 (if_then_else_M (EQ_M (to x6) (i 4))  qa02001011 O) ) .
Definition qa02011000_s := (if_then_else_M (EQ_M (to x6) (i 4)) qa02021000 (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa02111000 (if_then_else_M (EQ_M (to x6) (i 3))  qa02011010 O)))  .
Definition qa02001001_s := (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa02101001 (if_then_else_M (EQ_M (to x6) (i 3)) qa02001011 O) ) .

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 -> *)

Definition  qa01201000_s := (if_then_else_M (EQ_M (to x6) (i 2))  qa02201000 (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01211000 (if_then_else_M (EQ_M (to x6) (i 3)) qa01201001 O)))  .
Definition  qa01111000_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa02111000 (if_then_else_M (EQ_M (to x6) (i 2)) qa01211000 (if_then_else_M (EQ_M (to x6) (i 3)) qa01121000  O)))  .
Definition  qa01101001_s :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa02101001 (if_then_else_M (EQ_M (to x6) (i 2))  qa01201001 O)).


(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 -> *)

 Definition qa01011010_s  := (if_then_else_M (EQ_M (to x6) (i 2)) qa02011010 (if_then_else_M (EQ_M (to x6) (i 4)) qa01021010 O))  .
Definition  qa01001011_s := (if_then_else_M (EQ_M (to x6) (i 2)) qa02001011  O)  .


(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01011000 -> *)
(*
Definition qa02011000 :=  O. *)
Definition qa01021000_s :=   (if_then_else_M (EQ_M (to x6) (i 2)) qa02021000 (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01121000 (if_then_else_M (EQ_M (to x6) (i 3)) qa01021010 O)))  .

(***qa00000000 -> qa00001000 ->  qa01001000 ->   qa01001001-> *)

(****************************end qa01001000 **********)

(*************************start qa00001100 ************)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> *)

Definition qa00201100_s  := (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00211100 (if_then_else_M (EQ_M (to x6) (i 4)) qa00201101 O)).
Definition qa00111100_s :=  (if_then_else_M (EQ_M (to x6) (i 3))  qa00211100  (if_then_else_M (EQ_M (to x6) (i 4)) qa00121100 O)).
Definition qa00101101_s :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa00201101 O).
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001110 -> *)

Definition qa00011110_s :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00021110 O).
Definition qa00001111_s := O.

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00011100 -> *)

Definition   qa00021100_s  := (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00121100 (if_then_else_M (EQ_M (to x6) (i 3)) qa00021110 O)).

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001101 -> *)


(************** end qa00001100 ************)
(*************************start  qa00101000 ************)
(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 -> *)

Definition qa00211000_s := (if_then_else_M (EQ_M (to x6) (i 4)) qa00221000 (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01211000  (if_then_else_M (EQ_M (to x6) (i 2)) qa00211100 O))).
Definition qa00201001_s := (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01201001  (if_then_else_M (EQ_M (to x6) (i 2)) qa00201101 O)).

(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00111000 -> *)
(*Definition qa00211000 := O.*)
Definition qa00121000_s  := (if_then_else_M (EQ_M (to x6) (i 3))  qa00221000 (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01121000 (if_then_else_M (EQ_M (to x6) (i 2))  qa00121100 O))).


(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00101001 -> *)


(*************************end  qa00101000 ********)
(*********************start qa00001010 ************)

(***qa00000000 -> qa00001000 ->  qa00001010 ->  qa00011010 -> *)


Definition  qa00021010_s  :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01021010  (if_then_else_M (EQ_M (to x6) (i 3))  qa00021110  O)).

(***qa00000000 -> qa00001000 ->  qa00001010 ->  qa00001011 -> *)

 

(***********end qa00001010 ************)
(***********************start qa00011000 ****)

(***qa00000000 -> qa00001000 ->  qa00011000 -> qa00021000 -> *)

(***********************end qa00011000 ****)
(*********commented out qa00001001**********)

(************/// end qa00001000/// ***************)

(************/// start qa01000000/// ***************)

(******* start qa02000000 ************)

(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> *)

Definition qa02200000_s  := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12200000 (if_then_else_M (EQ_M (to x6) (i 1)) qa02201000 (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02210000 (if_then_else_M (EQ_M (to x6) (i 4)) qa02200001 O)))).

Definition qa02110000_s := (if_then_else_M (EQ_M (to x6) (i 3)) qa02210000  (if_then_else_M (EQ_M (to x6) (i 4)) qa02120000  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12110000 (if_then_else_M (EQ_M (to x6) (i 1)) qa02111000 O)))).


(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 -> *)

Definition qa02010010_s :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa02020010  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12010010 (if_then_else_M (EQ_M (to x6) (i 2)) qa02011010 O))).
Definition qa02000011_s :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12000011  (if_then_else_M (EQ_M (to x6) (i 1)) qa02001011 O)).

(***qa00000000 ->  qa01000000 ->  qa02000000 ->qa02010000 -> *)
Definition qa02020000_s := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12020000 (if_then_else_M (EQ_M (to x6) (i 1)) qa02021000 (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa02120000 (if_then_else_M (EQ_M (to x6) (i 2)) qa02020010 O)))).

(***qa00000000 ->  qa01000000 ->  qa02000000 ->qa02000001 -> *)

(******* end qa02000000 ************)
(******* start qa01100000 ************)
(*qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->*)

Definition qa01210000_s :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02210000 (if_then_else_M (EQ_M (to x6) (i 4)) qa01220000  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11210000 (if_then_else_M (EQ_M (to x6) (i 1)) qa01211000 O)))).
Definition qa01200001_s :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02200001 (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11200001 (if_then_else_M (EQ_M (to x6) (i 1))  qa01201001 O))).

(*qa00000000 -> qa01000000 -> qa01100000 ->  qa01110000 ->*)

Definition  qa01120000_s := (if_then_else_M (EQ_M (to x6) (i 2))  qa02120000 (if_then_else_M (EQ_M (to x6) (i 3))  qa01220000 (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11120000 (if_then_else_M (EQ_M (to x6) (i 1))  qa01121000 O)))).


(*qa00000000 -> qa01000000 -> qa01100000 -> qa01100001 ->*)


(******* end qa01100000 ************)
(******* start qa01000010************)
(*qa00000000 -> qa01000000 ->qa01000010 -> qa01010010 -> **)
(*
Definition qa02010010 := O. *)
Definition qa01020010_s := (if_then_else_M (EQ_M (to x6) (i 2)) qa02020010  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11020010 (if_then_else_M (EQ_M (to x6) (i 1)) qa01021010 O))).


(*qa00000000 -> qa01000000 ->qa01000010 ->  qa01000011-> **)


(******* end qa01000010************)

(**********qa01000001 commented out***********)
(************/// end qa01000000/// ***************)
(************/// start qa00000100/// ***************)
(*******start qa00000110************)

(*qa00000000 -> qa00000100 ->  qa00000110 -> qa00010110 -> **)

Definition qa00020110_s :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10020110 (if_then_else_M (EQ_M (to x6) (i 1))  qa00021110   O)).


(*qa00000000 -> qa00000100 ->  qa00000110 -> qa00000111 -> **)

(*******end qa00000110************)
(*********start qa00010100 ****************************)

(*qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 -> **)

Definition  qa00120100_s :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa00220100 (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10120100 (if_then_else_M (EQ_M (to x6) (i 1)) qa00121100 O))).


Definition qa00210100_s := (if_then_else_M (EQ_M (to x6) (i 4)) qa00220100  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10210100 (if_then_else_M (EQ_M (to x6) (i 1)) qa00211100 O))).

(*********end qa00010100 ****************************)
(********start qa00000101 **************************)
(*qa00000000 -> qa00000100 ->  qa00000101-> qa00100101 -> **)

Definition qa00200101_s := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10200101 (if_then_else_M (EQ_M (to x6) (i 1)) qa00201101 O)).

(********end qa00000101 **************************)


(************/// end qa00000100/// ***************)

(************/// start qa00100000/// ***************)
(******* start qa00200000************)

(*qa00000000 ->  qa00100000  -> qa00200000 -> qa00200100 -> **)


(*qa00000000 ->  qa00100000  -> qa00200000 -> qa00210000 -> **)

Definition qa00220000_s := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10220000 (if_then_else_M (EQ_M (to x6) (i 1)) qa00221000 (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01220000 (if_then_else_M (EQ_M (to x6) (i 2)) qa00220100 O)))).

(*qa00000000 ->  qa00100000  -> qa00200000 ->  qa00200001 -> **)

(*******end  qa00200000***)
(*****qa00100100 *****commented out**********)

(**start qa00110000****************************)
(*qa00000000 ->  qa00100000  ->  qa00110000 ->qa00120000 ->*)


(**end qa00110000****************************)
(*****start qa00100001**********************)
(*qa00000000 ->  qa00100000  ->   qa00100001 ->qa02100001 ->*)

Definition qa02200001_s := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) (*qa12200001*) O (if_then_else_M (EQ_M (to x6) (i 1))  O (*qa02201001*) O)).
Definition qa12100001_s := (if_then_else_M (EQ_M (to x6) (i 1))  (*qa22100001*) O (if_then_else_M (EQ_M (to x6) (i 3)) O (*qa12200001*) O)).
Definition qa02101001_s :=  (if_then_else_M (EQ_M (to x6) (i 3)) (*qa02201001*) O  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa02101001 O)). 

(*****end qa00100001**********************)

(************/// end qa00000010/// ***************)


(************/// start qa00010000/// ***************)
(**********************start qa00020000 ****************)
(*qa00000000 ->  qa00010000 -> qa00020000 ->qa01020000   ->*)


(**********************stop qa00020000 ****************)
(************/// end qa00010000/// ***************)


(************/// start qa00000001/// ***************)
(*********start  qa10000001  ***********************)
(*qa00000000 ->  qa00000001 -> qa10000001 ->  qa10100001  ->*)


(********end qa10000001 ***************************)
(************/// end qa00000001/// ***************)

 (*************qa00000000 -> qa10000000 -> qa20000000 -> *)

Definition qa21000000_ss :=   (if_then_else_M (EQ_M (to x6) (i 2))   qa22000000_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa21100000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa21000010_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa21010000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa21000001_s O))))).

Definition qa20000100_ss :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20100100_s (if_then_else_M (EQ_M (to x6) (i 3)) qa20000110_s   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa20010100_s  (if_then_else_M (EQ_M (to x6) (i 4))  qa20000101_s O)))).


Definition qa20100000_ss := (if_then_else_M (EQ_M (to x6) (i 3))  qa20200000_s  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21100000_s  (if_then_else_M (EQ_M (to x6) (i 2))  qa20100100_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa20110000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa20100001_s O))))).

Definition qa20000010_ss :=    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21000010_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa20000110_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa20010010_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa20000011_s O)))).
Definition qa20010000_ss := (if_then_else_M (EQ_M (to x6) (i 4)) qa20020000_s   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21010000_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa20010100_s   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20110000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa20010010_s   O))))).

Definition qa20000001_ss :=    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21000001_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa20000101_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20100001_s  (if_then_else_M (EQ_M (to x6) (i 3))  qa20000011_s O)))).

(*******************************qa00000000 -> qa10000000 ->qa11000000 ->*******************)
(**
Definition qa21000000:=  (if_then_else_M (EQ_M (to x6) (i 1))  acc (if_then_else_M (EQ_M (to x6) (i 2))  acc   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 97) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 97)   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 98)  (if_then_else_M (EQ_M (to x6) (i 4)) (grn 98) O)))))).

qa12000000, qa11100000, qa11000010, qa11010000,qa11000001*)
Definition qa12000000_ss := (if_then_else_M (EQ_M (to x6) (i 1)) qa22000000_s (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa12100000_s  (if_then_else_M (EQ_M (to x6) (i 3))  qa12000010_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa12010000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa12000001_s O))))).


Definition  qa11100000_ss :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa21100000_s (if_then_else_M (EQ_M (to x6) (i 2))  qa12100000_s  (if_then_else_M (EQ_M (to x6) (i 3))  qa11200000_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa11110000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa11100001_s O))))).

Definition  qa11000010_ss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa21000010_s  (if_then_else_M (EQ_M (to x6) (i 2))   qa12000010_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa11010010_s  (if_then_else_M (EQ_M (to x6) (i 4))  qa11000011_s O)))).
Definition qa11010000_ss :=   (if_then_else_M (EQ_M (to x6) (i 1)) qa21010000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa12010000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa11020000_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa11110000_s  (if_then_else_M (EQ_M (to x6) (i 3))  qa11010010_s O))))).


(************************qa00000000 -> qa10000000 -> qa10000100 ->***************************)

(*******************qa20000100, qa10100100, qa10000110, qa10010100, qa10000101*****************************)

Definition qa10100100_ss := (if_then_else_M (EQ_M (to x6) (i 1))   qa20100100_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa10200100_s     (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10110100_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa10100101_s O)))).


Definition qa10000110_ss :=   (if_then_else_M (EQ_M (to x6) (i 1))   qa20000110_s     (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa10010110_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa10000111_s O))).

Definition  qa10010100_ss :=   (if_then_else_M (EQ_M (to x6) (i 1))  qa20010100_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa10020100_s   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10110100_s   (if_then_else_M (EQ_M (to x6) (i 3)) qa10010110_s O)))).
Definition qa10000101_ss :=   (if_then_else_M (EQ_M (to x6) (i 1))  qa20000101_s     (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa10100101_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa10000111_s O))).

(***************************qa00000000 -> qa10000000 ->qa10100000->************************************************)
(*qa20100000, qa10200000, qa11100000, qa10100100, qa10110000, qa10100001*********)


Definition qa10200000_ss :=(if_then_else_M (EQ_M (to x6) (i 1))  qa20200000_s (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11200000_s  (if_then_else_M (EQ_M (to x6) (i 2))  qa10200100_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10210000_s  (if_then_else_M (EQ_M (to x6) (i 4))  qa10200001_s O))))).

Definition  qa10110000_ss := (if_then_else_M (EQ_M (to x6) (i 1))  qa20110000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa10210000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa10120000_s  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11110000_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa10110100_s  O))))).

Definition  qa10100001_ss := (if_then_else_M (EQ_M (to x6) (i 1))  qa20100001_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa10200001_s  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11100001_s  (if_then_else_M (EQ_M (to x6) (i 2))  qa10100101_s O)))).


(*****************************************qa00000000 -> qa10000000 ->qa10000010 -> ******************************************************************)
(****qa20000010, qa11000010, qa10000110, qa10010010,qa10000011****)

Definition  qa10010010_ss := (if_then_else_M (EQ_M (to x6) (i 1))  qa20010010_s (if_then_else_M (EQ_M (to x6) (i 4))  qa10020010_s  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11010010_s  (if_then_else_M (EQ_M (to x6) (i 2))  qa10010110_s O)))).

Definition qa10000011_ss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa20000011_s (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11000011_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa10000111_s O))).

(**************qa00000000 -> qa10000000 -> qa10010000 ->****************)
(****qa20010000,qa10020000, qa11010000, qa10010100, qa10110000,qa10010010****)


Definition qa10020000_ss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa20020000_s  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11020000_s  (if_then_else_M (EQ_M (to x6) (i 2))  qa10020100_s (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa10120000_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa10020010_s O))))).




(************************qa00000000 -> qa10000000 -> qa10000001 -> ******************************)
(****** qa20000001,  qa11000001  qa10000101 qa10100001 qa10000011 **)

Definition   qa11000001_ss := (if_then_else_M (EQ_M (to x6) (i 1))   qa21000001_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa12000001_s (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa11100001_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa11000011_s O)))).

(*************************qa00000000 -> qa00001000 -> qa01001000 ->******************************)
(*******qa01001000**************************************)
(*qa02001000 qa01101000 qa01001010 qa01011000 qa01001001 *)


Definition qa02001000_ss :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))   qa02101000_s   (if_then_else_M (EQ_M (to x6) (i 3))  qa02001010_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa02011000_s  (if_then_else_M (EQ_M (to x6) (i 4))  O O)))).

Definition  qa01101000_ss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02101000_s  (if_then_else_M (EQ_M (to x6) (i 3))  qa01201000_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa01111000_s  (if_then_else_M (EQ_M (to x6) (i 4))  qa01101001_s O)))). 
Definition  qa01001010_ss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02001010_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa01011010_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa01001011_s O))). 
Definition  qa01011000_ss :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02011000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa01021000_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa01111000_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa01011010_s O)))). 
Definition  qa01001001_ss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02001001_s    (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01101001_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa01001001_s O))).



(*********** qa00000000 -> qa00001000 ->qa00001100 -> ****)
(*qa00101100 qa00001110 qa00011100 qa00001101 *************)


Definition qa00101100_ss := (if_then_else_M (EQ_M (to x6) (i 3))  qa00201100_s   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00111100_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa00101101_s O))).
Definition   qa00001110_ss :=  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00011110_s  (if_then_else_M (EQ_M (to x6) (i 4))  qa00001111_s O)).
Definition  qa000011100_ss := (if_then_else_M (EQ_M (to x6) (i 4))  qa00021100_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00111100_s  (if_then_else_M (EQ_M (to x6) (i 3))  qa00111100_s O))).

Definition  qa00001101_ss :=   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00101101_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa00001111_s O)).

(**** qa00000000 -> qa00001000 -> qa00101000 -> **************************)

(***qa00201000 qa01101000 qa00101100 qa00111000 qa00101001****)

Definition qa00201000_ss := (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01201000_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa00201100_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa00211000_s (if_then_else_M (EQ_M (to x6) (i 4)) qa00201001_s O)))).

Definition  qa00111000_ss :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa00211000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa00121000_s  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01111000_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa00111100_s O)))).
Definition  qa00101001_ss :=   (if_then_else_M (EQ_M (to x6) (i 3)) qa00201001_s   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01101001_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa00101101_s O))).

(***** qa00000000 -> qa00001000 -> qa00001010 ->********************************)
(*** qa01001010  qa00001110  qa00011010  qa00001011 *)

Definition  qa00011010_ss := (if_then_else_M (EQ_M (to x6) (i 4))  qa00021010_s   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01011010_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa00011110_s  O))).
Definition  qa00001011_ss  :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01001011_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa00001111_s O)).


(*********qa00000000 -> qa00001000 ->qa00011000 ->******************************)
(***qa00021000 qa01011000 qa00011100 qa00111000 qa00011010 *)

Definition qa00021000_ss := (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01021000_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa00021100_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00121000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa00021010_s O)))).

(***********qa00000000 -> qa00001000 ->qa00001001->********************************)


(****************************qa00000000 -> qa01000000 -> qa02000000 ->*****************)
(**qa12000000, qa02001000, qa02100000, qa02000010, qa02010000, qa02000001************)

Definition  qa02100000_ss :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa02200000_s (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa12100000_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa02101000_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02110000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa02100001_s O))))).
Definition  qa02000010_ss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12000010_s (if_then_else_M (EQ_M (to x6) (i 1)) qa02001010_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02010010_s  (if_then_else_M (EQ_M (to x6) (i 4))  qa02000011_s O)))).
Definition  qa02010000_ss :=  (if_then_else_M (EQ_M (to x6) (i 4))  qa02020000_s (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))qa12010000_s  (if_then_else_M (EQ_M (to x6) (i 1)) qa02011000_s (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa02110000_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa02010010_s O))))).
Definition  qa02000001_ss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12000001_s  (if_then_else_M (EQ_M (to x6) (i 1)) qa02001001_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa02100001_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa02000011_s O)))).

(***************qa00000000 -> qa01000000 -> qa01100000 ->***********************)
(**qa02100000, qa01200000, qa11100000, qa01101000, qa01110000, qa01100001************)


Definition  qa01200000_ss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02200000_s (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11200000_s  (if_then_else_M (EQ_M (to x6) (i 1)) qa01201000_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01210000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa01200001_s O))))).

Definition  qa01110000_ss :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02110000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa01210000_s (if_then_else_M (EQ_M (to x6) (i 4)) qa01120000_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11110000_s  (if_then_else_M (EQ_M (to x6) (i 1)) qa01111000_s  O))))).


Definition  qa01100001_ss := (if_then_else_M (EQ_M (to x6) (i 2)) qa02100001_s (if_then_else_M (EQ_M (to x6) (i 3)) qa01200001_s   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11100001_s  (if_then_else_M (EQ_M (to x6) (i 1)) qa01101001_s  O)))).
 
(****************************qa00000000 -> qa01000000 ->qa01000010 ->**************************************)



Definition  qa01010010_ss :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02010010_s (if_then_else_M (EQ_M (to x6) (i 4)) qa01020010_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11010010_s (if_then_else_M (EQ_M (to x6) (i 1)) qa01011010_s  O)))).
Definition  qa01000011_ss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02000011_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11000011_s (if_then_else_M (EQ_M (to x6) (i 1)) qa01001011_s   O))).


 (*****************///end qa01000000///**********************************************)
(***********************************************************************************)


(*****************///start qa00000100///**********************************************)
(***********************************************************************************)


 (*****************************qa00000000 -> qa00000100 -> qa00000110 ->********************************)

Definition  qa00010110_ss :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00020110_s   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10010110_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00011110_s  O))).
Definition qa00000111_ss :=    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000111 (if_then_else_M (EQ_M (to x6) (i 1)) qa00001111  O)).
(************qa00000000 -> qa00000100 ->qa00010100 ->**************************)
(*qa00020100, qa10010100 , qa00011100 , qa00110100, qa00010110***)
Definition qa00020100_ss :=    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10020100_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00021100_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa00120100_s (if_then_else_M (EQ_M (to x6) (i 3)) qa00020110_s  O)))).


Definition  qa00110100_ss :=  (if_then_else_M (EQ_M (to x6) (i 3))  qa00210100_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa00120100_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10110100_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00111100_s  O)))).

(**********************qa00000000 -> qa00000100 -> qa00000101 ->**************************************************************)
(* qa10000101,  qa00001101 ,  qa00100101   qa00000111 *)

Definition   qa00100101_ss := (if_then_else_M (EQ_M (to x6) (i 3))  qa00200101_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10100101_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00101101_s O))).

(*****************///end qa00000100///**********************************************)
(***********************************************************************************)


(*****************///start  qa001000000 ///**********************************************)
(***********************************************************************************)
(************qa00000000 -> qa001000000 -> qa00200000 ->*)
(*qa10200000, qa00201000 , qa01200000, qa00200100,qa00210000, qa00200001*)

Definition  qa00200100_ss :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10200100_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00201100_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00210100_s (if_then_else_M (EQ_M (to x6) (i 4)) qa00200101_s O)))).

Definition qa00210000_ss :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00220000_s (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10210000_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00211000_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa01210000_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00210100_s O))))).
Definition  qa00200001_ss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10200001_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00201001_s  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01200001_s (if_then_else_M (EQ_M (to x6) (i 2)) qa00200101_s O)))).


(************qa00000000 -> qa00100000 -> qa00100100 ->***********************)
(* qa00200100, qa10100100, qa00101100, qa00110100 qa00100101 *)

(************qa00000000 -> qa001000000 -> qa00110000 ->*********************)
(*qa00210000 qa00120000 qa10110000 qa00111000 qa01110000 qa00110100*)

Definition  qa00120000_ss :=  (if_then_else_M (EQ_M (to x6) (i 3))  qa00220000_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10120000_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00121000_s  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01120000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa00120100_s O))))).

(****************qa00000000 -> qa00100000 -> qa00100001->******************************)
(*qa00200001 qa10100001 qa00101001 qa02100001 qa00100101*)


Definition  qa02100001_ss := (if_then_else_M (EQ_M (to x6) (i 3))  qa02200001_s    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12100001_s (if_then_else_M (EQ_M (to x6) (i 1)) qa02101001_s O))).


(*****************///end  qa00100000 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00000010 ///**********************************************)
(***********************************************************************************)
(*****************qa00000000 -> qa00000010 ->  qa00010010 ->**)
(** qa00020010  qa10010010  qa00011010  qa01010010  qa00010110**)
Definition  qa00020010_ss :=    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10020010_s  (if_then_else_M (EQ_M (to x6) (i 1)) ( qa00021010_s)  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa01020010_s (if_then_else_M (EQ_M (to x6) (i 1))  qa00020110_s O)))).

(***********qa00000000 -> qa00000010 ->qa00000011->***************************)

(**qa10000011 qa00001011 qa01000011 qa00000111**)

(*****************///end   qa00000010 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00010000 ///**********************************************)
(***********************************************************************************)
(**********qa00000000 -> qa00010000 -> qa00020000 -> ***)
(*qa10020000, qa00021000, qa01020000 , qa00020100 , qa00120000 qa00020010*)



Definition  qa01020000_ss  :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02020000_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11020000_s (if_then_else_M (EQ_M (to x6) (i 1))  qa01021000_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa01120000_s (if_then_else_M (EQ_M (to x6) (i 3))  qa01020010_s O))))).

(**qa00000000 -> qa00010000 ->qa01010000 ->***)



(*****************///end  qa00010000 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00000001 ///**********************************************)
(***********************************************************************************)
(**********qa00000000 -> qa00000001 -> qa10000001 ->*)



(***************qa00000000 -> qa00000001 -> qa00001001 ->**********)

(****qa01001001 qa00001101 qa00101001 qa00001011 *)

(** qa00000000 -> qa00000001 -> qa01000001 ->*)

(*** qa02000001  qa11000001  qa01001001 qa01100001  qa01000011 ****)


(*****************///end  qa00000001 ///**********************************************)
(***********************************************************************************)

(**************************************************************************************************)
(**************************************************************************************************)



Definition qa20000000_sss:=    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21000000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa20000100_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20100000_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa20000010_ss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa20010000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa20000001_ss O)))))).
Definition qa11000000_sss := (if_then_else_M (EQ_M (to x6) (i 1))  qa21000000_ss (if_then_else_M (EQ_M (to x6) (i 2)) qa12000000_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa11100000_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa11000010_ss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa11010000_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa20000001_ss O)))))).
Definition qa10000100_sss:= (if_then_else_M (EQ_M (to x6) (i 1))  qa20000100_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10100100_ss (if_then_else_M (EQ_M (to x6) (i 3)) qa10000110_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10010100_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa10000101_ss O))))).

Definition qa10100000_sss:= (if_then_else_M (EQ_M (to x6) (i 1))  qa20100000_ss  (if_then_else_M (EQ_M (to x6) (i 3))   qa10200000_ss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11100000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa10100100_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa10110000_ss   (if_then_else_M (EQ_M (to x6) (i 4)) qa10100001_ss O)))))).
Definition qa10000010_sss := (if_then_else_M (EQ_M (to x6) (i 1))  qa20000010_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11000010_ss  (if_then_else_M (EQ_M (to x6) (i 2))  qa10000110_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))qa10010010_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa10000011_ss O))))).

Definition qa10010000_sss:=  (if_then_else_M (EQ_M (to x6) (i 1)) qa20010000_ss  (if_then_else_M (EQ_M (to x6) (i 4))   qa10020000_ss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11010000_ss (if_then_else_M (EQ_M (to x6) (i 2))  qa10010100_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10110000_ss (if_then_else_M (EQ_M (to x6) (i 3))  qa10010010_ss  O)))))).

Definition qa10000001_sss:= (if_then_else_M (EQ_M (to x6) (i 1)) qa20000001_ss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11000001_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa10000101_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10100001_ss  (if_then_else_M (EQ_M (to x6) (i 3))  qa10000011_ss O))))).


(*******************qa00001000*******************************************************)


Definition qa01001000_sss := (if_then_else_M (EQ_M (to x6) (i 2))  qa02001000_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa01101000_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa01001010_ss   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01011000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01001001_ss O))))).

Definition qa00001100_sss := (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00101100_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00001110_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (*qa00011100_s*) O (if_then_else_M (EQ_M (to x6) (i 4))  qa00001101_ss O)))).

Definition qa00101000_sss := (if_then_else_M (EQ_M (to x6) (i 3))   qa00201000_ss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01101000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) 
qa00101100_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00111000_ss (if_then_else_M (EQ_M (to x6) (i 4))  qa00101001_ss O))))).


Definition qa00001010_sss :=    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))
 qa01001010_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00001110_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa00011010_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa00001011_ss O)))).

Definition qa00011000_sss :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00021000_ss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01011000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) (*qa00011100_s*) O  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00111000_ss (if_then_else_M (EQ_M (to x6) (i 3))  qa00011010_ss O))))).

Definition qa00001001_sss :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01001001_ss  (if_then_else_M (EQ_M (to x6) (i 2))  qa00001101_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00101001_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00001011_ss O)))).


(**************************qa01000000*******************************************************)




Definition qa02000000_sss := (if_then_else_M (EQ_M (to x6) (i 2)) qa12000000_ss   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa02100000_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa02000010_ss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa02010000_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa02000001_ss O))))).


Definition qa01100000_sss  :=    (if_then_else_M (EQ_M (to x6) (i 2))  qa02100000_ss  (if_then_else_M (EQ_M (to x6) (i 3))  qa01200000_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11100000_ss  (if_then_else_M (EQ_M (to x6) (i 1))  qa01101000_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01110000_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa01100001_ss O)))))).

Definition qa01000010_sss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02000010_ss   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11000010_ss  (if_then_else_M (EQ_M (to x6) (i 1))  qa01001010_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01010010_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01000011_ss O))))).

Definition qa01010000_sss := (if_then_else_M (EQ_M (to x6) (i 2))  qa02010000_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa01020000_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11010000_ss  (if_then_else_M (EQ_M (to x6) (i 1)) qa01011000_ss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01110000_ss (if_then_else_M (EQ_M (to x6) (i 3)) qa01010010_ss O)))))).

Definition qa01000001_sss:=  (if_then_else_M (EQ_M (to x6) (i 2))   qa02000001_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11000001_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa01001001_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa01100001_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa01000011_ss O))))).


(**************************qa00000100*******************************************************)




Definition qa00000110_sss :=    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10000110_ss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00001110_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00010110_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa00000111_ss O)))).

Definition qa00010100_sss:=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00020100_ss    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10010100_ss  (if_then_else_M (EQ_M (to x6) (i 1)) (*qa00011100_s *) O  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa00110100_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00010110_ss O))))).

Definition qa00000101_sss :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000101_ss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00001101_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00100101_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00000111_ss O)))).


(**************************qa001000000*******************************************************)

Definition qa00200000_sss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10200000_ss  (if_then_else_M (EQ_M (to x6) (i 1)) qa00201000_ss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01200000_ss (if_then_else_M (EQ_M (to x6) (i 2)) qa00200100_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa00210000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00200001_ss O)))))).


Definition qa00100100_sss :=  (if_then_else_M (EQ_M (to x6) (i 3))  qa00200100_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10100100_ss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00101100_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00110100_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa00100101_ss O))))).

Definition qa00110000_sss := (if_then_else_M (EQ_M (to x6) (i 3))  qa00210000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00120000_ss    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10110000_ss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00111000_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01110000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00110100_ss O)))))).

Definition qa00100001_sss := (if_then_else_M (EQ_M (to x6) (i 3)) qa00200001_ss   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10100001_ss  (if_then_else_M (EQ_M (to x6) (i 1)) qa00101001_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa02100001_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00100101_ss O))))).

(**************************qa00000010*******************************************************)



Definition qa00010010_sss:=  (if_then_else_M (EQ_M (to x6) (i 4))  qa00020010_ss   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10010010_ss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00011010_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01010010_ss (if_then_else_M (EQ_M (to x6) (i 2))  qa00010110_ss O))))).

Definition qa00000011_sss :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa10000011_s  (if_then_else_M (EQ_M (to x6) (i 2))  qa00001011_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01000011_s  (if_then_else_M (EQ_M (to x6) (i 3))  qa00000111_s O)))).

(**************************qa00010000*******************************************************)




Definition qa00020000_sss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10020000_ss (if_then_else_M (EQ_M (to x6) (i 1))  qa00021000_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01020000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00020100_ss     (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00120000_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00020010_ss O)))))) .



(**************************qa00000001*******************************************************)










Definition qa10000000_ssss :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M (EQ_M (to x6) (i 1)) qa20000000_sss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11000000_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa10000100_sss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10100000_sss (if_then_else_M (EQ_M (to x6) (i 3)) qa10000010_sss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10010000_sss (if_then_else_M (EQ_M (to x6) (i 4)) qa10000001_sss O))))))))))).

Definition qa00001000_ssss :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) & (EQ_M (to x6) (i 1)) mx1rn2 (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01001000_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00001100_sss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa00101000_sss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00001010_sss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00011000_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00001001_sss O)))))))))).


Definition qa01000000_ssss :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M (EQ_M (to x6) (i 2)) qa02000000_sss (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11000000_sss  (if_then_else_M (EQ_M (to x6) (i 1))  qa01001000_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01100000_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa01000010_sss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01010000_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01000001_sss O))))))))))).

 Definition qa0000100_ssss :=  (if_then_else_M (EQ_M (reveal x6) (i 2) ) & (EQ_M (to x6) (i 2)) mx1rn2 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01001000_sss  (if_then_else_M (EQ_M (to x6) (i 2))  qa00001100_sss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00101000_sss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00001010_sss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))   qa00011000_sss (if_then_else_M (EQ_M (to x6) (i 4))  qa00001001_sss O)))))))))).

 Definition qa00100000_ssss :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qa02000000_sss (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11000000_sss (if_then_else_M (EQ_M (to x6) (i 1))  qa01001000_sss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01100000_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa01000010_sss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa01010000_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01000001_sss O))))))))))).

Definition  qa00000010_ssss  :=   (if_then_else_M (EQ_M (reveal x6) (i 3) ) & (EQ_M (to x6) (i 3)) mx1rn2 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (reveal x6) (i 2) ) O   (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000100_sss (if_then_else_M (EQ_M (to x6) (i 4)) qa00001100_sss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa00101000_sss  (if_then_else_M (EQ_M (to x6) (i 2))  qa00000110_sss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa00010100_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00000101_sss O)))))))))).

Definition  qa00010000_ssss  :=    (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O  (if_then_else_M (EQ_M (to x6) (i 4)) qa00200000_sss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10100000_sss  (if_then_else_M (EQ_M (to x6) (i 1)) qa00101000_sss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01100000_sss  (if_then_else_M (EQ_M (to x6) (i 2))   qa00100100_sss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00110000_sss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00100001_sss O))))))))))).
Definition  qa00000001_ssss := (if_then_else_M (EQ_M (reveal x6) (i 4) ) & (EQ_M (to x6) (i 4)) mx1rn2 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (reveal x6) (i 2) ) O   (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000001_sss  (if_then_else_M (EQ_M (to x6) (i 1)) qa00001001_sss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01000001_sss (if_then_else_M (EQ_M (to x6) (i 2)) qa00000101_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00100001_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00000011_sss O)))))))))).



(********************************************************************)


Definition t17 :=  msg  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000000_ssss (if_then_else_M (EQ_M (to x6) (i 1)) qa00001000_ssss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01000000_ssss (if_then_else_M (EQ_M (to x6) (i 2)) qa00001000_ssss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00100000_sss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00000010_ssss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00010000_ssss  (if_then_else_M (EQ_M (to x6) (i 4))  qa00000001_ssss O)) ))) ) )))))).


Definition phi6:= phi5 ++ [t17]. 







(***********************************************@@@phi7@@@********************************************************)
(************************************************************************************************************)
(************************************************************************************************************)

Definition mphi6 := (conv_mylist_listm phi6).
Definition x7 := (f mphi6).

(************/// start qa10000000/// ***************)

(********************************start qa20000000******************************)
(***/// qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ///***)
(********///qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> qa22000000 ->/// *********)

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> qa22000000 ->qa22100000 -> *********)

Definition qa22200000 := (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 277) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 277) O) ).
Definition qa22110000 := (if_then_else_M (EQ_M (to x6) (i 3)) (grn 279) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 279) O)).
Definition qa22100001 := (if_then_else_M (EQ_M (to x6) (i 3)) (grn 279) O).
(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> qa22000000 -> qa22000010 -> *********)

 Definition qa22010010 :=  (if_then_else_M (EQ_M (to x6) (i 4)) (grn 279) O).
Definition  qa22000011 := O.
 
(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> qa22000000 -> qa22010000 -> *********)
Definition qa22020000 :=  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 277) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 277) O)).
(*Definition qa22110000 := (if_then_else_M (EQ_M (to x6) (i 3)) (grn 279) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 279) O)).*)
(*Definition qa22010010 := (if_then_else_M (EQ_M (to x6) (i 4)) (grn 279) O).*)

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> qa22000000 ->  qa22000001 -> *********)
(*Definition qa22100001 := O.*)
(*Definition qa22000011 := O.*)

 
(********/// qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21100000 ->/// *********)

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21100000 ->qa21200000-> *********)

(*Definition qa22200000 := O.*)
Definition qa21210000 := (if_then_else_M (EQ_M (to x6) (i 2)) (grn 279) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 279) O)).
Definition qa21200001 := (if_then_else_M (EQ_M (to x6) (i 2)) (grn 279) O).
(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21100000 -> qa21110000-> *********)
(*Definition qa22110000 := O.*)
(*Definition qa21210000 := O.*)
Definition qa21120000 := (if_then_else_M (EQ_M (to x6) (i 2)) acc (if_then_else_M (EQ_M (to x6) (i 3)) acc O)).

(******** ///qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21000010  ->/// *********)
(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21000010  -> qa21010010 -> *********)

Definition qa21020010 :=  (if_then_else_M (EQ_M (to x6) (i 2)) acc O).
(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21000010  -> qa21000011 -> *********)
(*Definition qa22000011 := O. *)

(********///qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21010000  ->/// *********)

(********qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21010000  ->qa21020000 -> *********)

(*Definition qa22020000 := O.*)
(*Definition qa21120000 :=  (if_then_else_M (EQ_M (to x6) (i 2)) acc  (if_then_else_M (EQ_M (to x6) (i 3)) acc O)).*)
(*Definition qa21020010:= O.*)



(*********/// qa00000000 -> qa10000000 -> qa20000000 ->  qa20000100 ->///*************)
(*********///qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20100100->///*****************************************)
(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20100100-> qa20200100 ->*****************************************)
Definition qa20210100 := (if_then_else_M (EQ_M (to x6) (i 4))  acc O).
Definition qa20200101 :=  O.
(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20100100-> qa20110100 ->*****************************************)
(*Definition qa20210100 := O.*)
Definition qa20120100 := (if_then_else_M (EQ_M (to x6) (i 3))  acc O).
(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20100100-> qa20100101 ->*****************************************)
(*Definition qa20200101 := O.*)
(*********///qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20000110->///**********)
(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20000110-> qa20010110 ->**********)

Definition qa20020110 := O.
(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20000110-> qa20000111 ->**********)
(*Definition qa20000111 := O. *)
(*********///qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20010100 ->///**********)
(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20010100 ->  qa20020100 ->**********)
(*Definition qa20120100 := O.*)
 (*Definition qa20020110 := O.*)
 
 
(****///qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->///*************)

 (****///qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20200000->///*************)
(****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20200000->  qa20210000 ->*************)


Definition qa20220000 := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) (grn 283) (if_then_else_M (EQ_M (to x6) (i 1)) (grn 283) O) ).
(*Definition qa21210000 := (if_then_else_M (EQ_M (to x6) (i 2))  acc (if_then_else_M (EQ_M (to x6) (i 4))  acc O)).*)
(*Definition  qa20210100 := O.*)


(****///qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20110000->///*************)
 (****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20110000-> qa20120000 ->*************)

(*Definition qa20220000 := O.*)
(*Definition qa21120000 := O. *)
(*Definition qa20120100 := O. *)
(****///qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20100001->///*************)
(****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20100001->qa20200001 ->*************)

(*Definition qa21200001 := O.*)
(*Definition qa20200101 := O.*)


(************************///qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 ->///**********)
(**************************///qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 -> qa20010010 ->///************* *************)
(**************************qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 -> qa20010010 -> qa20020010 ->************* *************)
(*Definition qa21020010 := O.*)
(*Definition qa20020110 := O.*)






(***********************end  qa20000000********************************)


(*************************start  qa11000000 **************************)

(******** /// qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 /// -> *)
(********/// qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 -> qa12100000 -> /// *)
(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 -> qa12100000 -> qa12200000 -> *)
(*Definition qa22200000 := O.*)
Definition qa12210000 :=   (if_then_else_M (EQ_M (to x6) (i 1)) acc  (if_then_else_M (EQ_M (to x6) (i 4)) acc O)).
Definition qa12200001 :=   (if_then_else_M (EQ_M (to x6) (i 1)) acc O).
(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 -> qa12100000 -> qa12110000 -> *)
(*Definition qa22110000 := (if_then_else_M (EQ_M (to x6) (i 1)) acc  (if_then_else_M (EQ_M (to x6) (i 4)) acc (if_then_else_M (EQ_M (to x6) (i 1)) acc O))).*)
(*Definition qa12210000 := O. *)
Definition qa12120000 := (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 3)) acc O)).
(********/// qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->  qa12000010 -> /// *)
(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->  qa12000010 -> qa12010010 ->  *)

(*Definition qa22010010 :=  O.*)
Definition qa12020010 :=  (if_then_else_M (EQ_M (to x6) (i 1)) acc O).


(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->  qa12000010 -> qa12000011->  *)

(*Definition qa22000011 := O.*)


(********/// qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->  qa12010000 -> /// *)
(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->  qa12010000 -> qa12020000 ->  *)

(*Definition qa22020000 := O.*)
(*Definition qa12120000 := O.*)
(*Definition qa12020010 := O.*)

(***///qa00000000 -> qa10000000 -> qa11000000 ->qa11100000->///******************)
(***///qa00000000 -> qa10000000 -> qa11000000 ->qa11100000-> qa11200000->///******************)
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000-> qa11200000->qa11210000 ->******************)
(*Definition qa21210000 := O.*)
(*Definition qa12210000 := O. *)
Definition qa11220000 :=   (if_then_else_M (EQ_M (to x6) (i 1)) acc (if_then_else_M (EQ_M (to x6) (i 2)) acc O)).
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000-> qa11200000->qa11200001 ->******************)
(*Definition qa21200001 := O. *)
(*Definition qa12200001 := O.*)

 
(***///qa00000000 -> qa10000000 -> qa11000000 ->qa11100000-> qa11110000->///******************)
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000-> qa11110000-> qa11120000 ->******************)

(*Definition qa21120000 := O. *)
(*Definition qa12120000 := O. *)
(*Definition qa11220000 := O.*)

(*************///qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 ->/// ****************)
(*************///qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 -> qa11010010->/// ****************)
(*************qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 -> qa11010010->qa11020010 -> ****************)

(*Definition qa21020010 := (if_then_else_M (EQ_M (to x6) (i 2)) acc  O). *)
(*Definition qa12020010 :=  O. *)






(*****************end qa11000000 **********************************************)

(****************start qa10000100 ********************************************)
(********/// qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->///  *)
(********/// qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->  qa10200100-> ///*)
(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->  qa10200100-> qa10210100 -> *)

(*Definition qa20210100 := O. *)
Definition  qa10220100 :=  (if_then_else_M (EQ_M (to x6) (i 1)) acc O).
(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->  qa10200100->  qa10200101 -> *)

 (*Definition qa20200101 := O.*)
 (********/// qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->   qa10110100->/// *)
(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->   qa10110100->qa20110100 -> *)
(*Definition qa20210100 :=   (if_then_else_M (EQ_M (to x6) (i 4)) acc O). *)
(*Definition qa20120100 :=  O.*)


(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->   qa10110100-> qa10120100 -> *)
(*Definition qa20120100 := O.*)
(*Definition qa10220100 := O. *)



(*************** /// qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 ->///*********)
(*************** /// qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 -> qa10010110 ->/// *********)
(***************  qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 -> qa10010110 -> qa10020110 -> *********)
(*Definition qa20020110 := O. *)






(******************end   qa10000100 ***********************)

(*****************************start qa10100000 **********)

(******** ///qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 ->///   *)
(********/// qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 -> qa10210000->///  *)
(******** qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 -> qa10210000-> qa10220000 -> *)
(*Definition qa20220000 := O. *)
(*Definition qa11220000 := O. *)
(*Definition qa10220100 := O. *)




(*****************************end qa10100000 **********)


(*****************************start qa10000010 **********)
(********/// qa00000000 -> qa10000000 -> qa10000010 -> qa10010010 ->///  *)

(******** qa00000000 -> qa10000000 -> qa10000010 -> qa10010010 -> qa10020010  ->  *)






(*****************************end qa10000010 **********)

(*****************************start qa10010000 **********)



(*****************************end qa10010000 **********)


(*****************************start qa10000001 **********)




(********************end qa10000001 **********************************)


(************/// end qa10000000/// ***************)

(**********************************************************************************************)

(************/// start qa00001000/// ***************)

(****************************start qa01001000 **********)
(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 ->/// *)
(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> qa02101000 ->/// *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> qa02101000 -> qa02201000 -> *)

Definition  qa02211000 := (if_then_else_M (EQ_M (to x6) (i 4)) acc O).
Definition  qa02201001 := O.
(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> qa02101000 -> qa02111000 -> *)
(*Definition qa02211000 := O. *)
Definition qa02121000 :=  (if_then_else_M (EQ_M (to x6) (i 3)) acc O).

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 ->  qa02001010 -> qa02011010 -> *)
Definition qa02021010 := O.

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 ->  qa02011000->qa02021000 -> *)

(*Definition qa02121000 := O. *)
(*Definition qa02021010 := O. *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> qa02001001  -> *)
(*Definition qa02101001 := O.*)
(*Definition qa02001011 := O.*)
(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->/// *)

(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->  qa01201000 -> ///*)
(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->  qa01201000 -> qa01211000 -> *)

(*Definition qa02211000 := O. *)
Definition qa01221000 :=   (if_then_else_M (EQ_M (to x6) (i 2)) acc O).
(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->  qa01201000 ->qa01201001 -> *)
(*Definition qa02201001 := O. *)
(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->  qa01111000  ->/// *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->  qa01111000  -> qa01121000 -> *)

(*Definition qa02121000 := O. *)
(*Definition qa01221000 := O. *)

(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 ->/// *)

(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 ->  qa01011010 ->/// *)
(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 ->  qa01011010 -> qa01021010 -> *)
 
(*Definition qa02021010 := O.*)



(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01011000 ->/// *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01011000 -> qa01021000 -> *)


(***///qa00000000 -> qa00001000 ->  qa01001000 ->   qa01001001->/// *)
(***qa00000000 -> qa00001000 ->  qa01001000 ->   qa01001001-> *)

(****************************end qa01001000 **********)

(*************************start qa00001100 ************)
(***///qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> /// *)
(***///qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> qa00201100 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> qa00201100 -> qa00211100 -> *)
Definition qa00221100 := O.
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> qa00201100 ->  qa00201101-> *)

 (***///qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 ->   qa00111100  ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 ->   qa00111100  ->  qa00121100 -> *)
(*Definition  qa00211100 := O.*)
(* Definition qa00221100 := O. *)
 

(**///*qa00000000 -> qa00001000 ->  qa00001100 -> qa00001110 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001110 -> qa00011110 -> *)
(*
Definition qa00021110 := O.
*)
 


(************** end qa00001100 ************)
(*************************start  qa00101000 ************)
(***///qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 ->/// *)
(***///qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 ->qa00211000 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 ->qa00211000 -> qa00221000 -> *)
(*Definition qa01221000 := O. *)
(*Definition qa00221100 := O. *)


(***///qa00000000 -> qa00001000 ->  qa00101000 -> qa00111000 -> ///*)


(*************************end  qa00101000 ********)
(*********************start qa00001010 ************)

(***///qa00000000 -> qa00001000 ->  qa00001010 ->  qa00011010 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001010 ->  qa00011010 ->  qa00021010 -> *)

(*Definition qa01021010 := O. *)
(*Definition  qa00021110 := O.*)
 


(***********end qa00001010 ************)
(***********************start qa00011000 ****)


(***********************end qa00011000 ****)
(*********commented out qa00001001**********)

(************/// end qa00001000/// ***************)

(************/// start qa01000000/// ***************)

(******* start qa02000000 ************)
(***///qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> ///*)
(***///qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> qa02200000 ->/// *)
(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> qa02200000 -> qa02210000 -> *)

Definition qa02220000 := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) (grn 240) (if_then_else_M (EQ_M (to x6) (i 1)) (grn 240) O)).
(*Definition qa12210000 := (if_then_else_M (EQ_M (to x6) (i 4)) acc O). *)
(*Definition qa02211000 := O. *)
(*Definition qa02200001 := O.*)

(***///qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 ->  qa02110000 ->/// *)
(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 ->  qa02110000 -> qa02120000 -> *)
(*Definition qa02220000 := O. *)
 (*Definition qa12120000 := O. *)
(*Definition qa02121000 := O. *)
(***///qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 ->/// *)
(***///qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 -> qa02010010 ->/// *)
(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 -> qa02010010 ->  qa02020010 -> *)
(*Definition  qa12020010 := O. *)
(*Definition qa02021010 := O. *)



(******* end qa02000000 ************)
(******* start qa01100000 ************)
(*///qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->///*)
(*///qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->qa01210000 ->/// *)
(*qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->qa01210000 -> qa01220000 -> *)

(*Definition qa02220000 :=  O. *)
(*Definition qa11220000 := O. *)
 (*Definition qa01221000 := O.  *)




(******* end qa01000010************)

(**********qa01000001 commented out***********)
(************/// end qa01000000/// ***************)
(************/// start qa00000100/// ***************)
(*******start qa00000110************)
(*///qa00000000 -> qa00000100 ->  qa00000110 -> qa00010110 ->/// **)
(*qa00000000 -> qa00000100 ->  qa00000110 -> qa00010110 -> qa00020110 -> **)

(*Definition qa10020110 := O. *)
(*Definition qa00021110 := O. *)



(*******end qa00000110************)
(*********start qa00010100 ****************************)
(*///qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 ->/// **)
(*///qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 -> qa00120100 ->/// **)
(*qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 -> qa00120100 -> qa00220100 -> **)
(*Definition qa10220100 := O. *)
(*Definition qa00221100 := O. *)


(*********end qa00010100 ****************************)
(********start qa00000101 **************************)
(*///qa00000000 -> qa00000100 ->  qa00000101-> qa00100101 ->/// **)
(*qa00000000 -> qa00000100 ->  qa00000101-> qa00100101 -> qa00200101 -> **)
(*Definition qa10200101 := O. *)
(*Definition qa00201101 := O. *)
(*Definition qa00200101 := O. *)


(********end qa00000101 **************************)


(************/// end qa00000100/// ***************)

(************/// start qa00100000/// ***************)
(******* start qa00200000************)



(*///qa00000000 ->  qa00100000  -> qa00200000 -> qa00210000 -> ///**)
(*qa00000000 ->  qa00100000  -> qa00200000 -> qa00210000 -> qa00220000 -> **)
(*Definition qa10220000 := O. *)
(*Definition qa00221000 := O. *)
(*Definition qa01220000 := O. *)
(*Definition qa00220100 := O. *)


(*****start qa00100001**********************)



(*****end qa00100001**********************)

(************/// end qa00000010/// ***************)


(************/// start qa00010000/// ***************)
(**********************start qa00020000 ****************)


(**********************stop qa00020000 ****************)
(************/// end qa00010000/// ***************)


(************/// start qa00000001/// ***************)
(*********start  qa10000001  ***********************)
(*qa00000000 ->  qa00000001 -> qa10000001 ->  qa10100001  ->*)


(********end qa10000001 ***************************)
(************/// end qa00000001/// ***************)
(*'sing ***********************)
(************/// start qa10000000/// ***************)

(********************************start qa20000000******************************)
(***/// qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ///***)
(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> qa22000000 -> *********)
(** qa22100000  qa22000010  qa22010000  qa22000001   *)
Definition qa22100000_s  := (if_then_else_M (EQ_M (to x6) (i 3))  qa22200000  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa22110000 (if_then_else_M (EQ_M (to x6) (i 4)) qa22100001 O) )).
Definition  qa22000010_s := (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa22010010 (if_then_else_M (EQ_M (to x6) (i 4)) qa22000011 O) ).
Definition  qa22010000_s := (if_then_else_M (EQ_M (to x6) (i 4)) qa22020000  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa22110000 (if_then_else_M (EQ_M (to x6) (i 3)) qa22010010 O) )).
Definition  qa22000001_s :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa22100001 (if_then_else_M (EQ_M (to x6) (i 3)) qa22000011 O) ).


(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21100000 -> *********)
(*
Definition qa22100000 := (if_then_else_M (EQ_M (to x6) (i 3))  acc    (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 167) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 167) O) )).
*)
Definition qa21200000_s :=(if_then_else_M (EQ_M (to x6) (i 2)) qa22200000  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa21210000 (if_then_else_M (EQ_M (to x6) (i 4)) qa21200001  O) )).
 Definition qa21110000_s := (if_then_else_M (EQ_M (to x6) (i 2))  qa22110000  (if_then_else_M (EQ_M (to x6) (i 3))  qa21210000   (if_then_else_M (EQ_M (to x6) (i 4))  qa21120000  O))).
Definition qa21100001_s :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa22100001  (if_then_else_M (EQ_M (to x6) (i 2))  qa21200001  O)).

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21000010  -> *********)
(*
Definition qa22000010  := (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 281) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 281) O) ). *)
Definition qa21010010_s  := (if_then_else_M (EQ_M (to x6) (i 2)) qa22010010  (if_then_else_M (EQ_M (to x6) (i 4))  qa21020010 O)).
Definition qa21000011_s  :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa22000011  O).

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21010000  -> *********)
(*Definition  qa22010000 := O.*)
Definition qa21020000_s := (if_then_else_M (EQ_M (to x6) (i 2)) qa21020000   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa21120000 (if_then_else_M (EQ_M (to x6) (i 3)) qa21020010 O) )).
(*Definition qa21110000 := O.
Definition  qa21010010 :=O *)

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 ->  qa21000001  -> *********)
(*
Definition qa22000001 := O. 
Definition qa21100001 := O.
Definition qa21000011 := O.*)

(*********/// qa00000000 -> qa10000000 -> qa20000000 ->  qa20000100 ->///*************)

(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20100100->*****************************************)
Definition  qa20200100_s :=  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa20210100 (if_then_else_M (EQ_M (to x6) (i 4))  qa20200101 O) ).
Definition qa20110100_s := (if_then_else_M (EQ_M (to x6) (i 3))  qa20210100 (if_then_else_M (EQ_M (to x6) (i 4))  qa20120100  O)).
Definition  qa20100101_s := (if_then_else_M (EQ_M (to x6) (i 3)) qa20200101  O).

(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20000110->**********)

Definition qa20010110_s := (if_then_else_M (EQ_M (to x6) (i 4)) 20020110 O).
Definition qa20000111_s := O.

(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->  qa20010100 ->**********)
Definition qa20020100_s := (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20120100  (if_then_else_M (EQ_M (to x6) (i 3)) qa20020110 O) ).

 (*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->   qa20000101 ->**********)

(****///qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->///*************)

 (****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20200000->*************)



Definition qa20210000_s := (if_then_else_M (EQ_M (to x6) (i 4)) qa20220000 O).
(*Definition  qa21200000 := (if_then_else_M (EQ_M (to x6) (i 2)) acc O).*)
(*Definition  qa20200100 := O.*)



 (****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20110000->*************)
(*Definition qa20210000 := O.*)
Definition qa20120000_s := (if_then_else_M (EQ_M (to x6) (i 3)) qa20220000 O).
(*Definition qa21110000 := (if_then_else_M (EQ_M (to x6) (i 2)) acc (if_then_else_M (EQ_M (to x6) (i 3)) acc (if_then_else_M (EQ_M (to x6) (i 4)) acc O))). *)
(*Definition qa20110100 := (if_then_else_M (EQ_M (to x6) (i 3)) acc (if_then_else_M (EQ_M (to x6) (i 4)) acc O)). *)


(****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->  qa20100001->*************)

Definition qa20200001_s :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21200001 (if_then_else_M (EQ_M (to x6) (i 3))  qa20200101 O) ).


(************************///qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 ->///**********)
(**************************qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 -> qa20010010 ->************* *************)
Definition qa20020010_s := (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21020010 (if_then_else_M (EQ_M (to x6) (i 3)) qa20020110 O) ).



(*******qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 -> qa20000011->*************)



(*********************///qa00000000 -> qa10000000 -> qa20000000 ->qa20010000->///*****)
(*******************qa00000000 -> qa10000000 -> qa20000000 ->qa20010000->qa20020000->**)
(*
Definition qa21020000 := O. *)
(*Definition qa20020100 := O.*)
(*Definition qa20120000 := O.*)
(*Definition qa20020010 := O.*)

(***********************end  qa20000000********************************)


(*************************start  qa11000000 **************************)

(******** /// qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 /// -> *)
(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 -> qa12100000 ->  *)


Definition qa12200000_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa22200000 (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa12210000 (if_then_else_M (EQ_M (to x6) (i 4)) qa12200001 O) ) ).

Definition qa12110000_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa22110000 (if_then_else_M (EQ_M (to x6) (i 3))qa12210000 (if_then_else_M (EQ_M (to x6) (i 4)) qa12120000 O))).

(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->  qa12000010 ->  *)


Definition qa12010010_s := (if_then_else_M (EQ_M (to x6) (i 1))  qa22010010 (if_then_else_M (EQ_M (to x6) (i 4))  qa12020010 O)).
Definition qa12000011_s :=   (if_then_else_M (EQ_M (to x6) (i 1)) qa22000011 O).

(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->  qa12010000 ->  *)


Definition qa12020000_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa22020000  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa12120000 (if_then_else_M (EQ_M (to x6) (i 3)) qa12020010 O) )).


(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 ->   qa12000001 ->  *)

(***///qa00000000 -> qa10000000 -> qa11000000 ->qa11100000->///******************)
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000-> qa11200000->******************)


Definition qa11210000_s  := (if_then_else_M (EQ_M (to x6) (i 1)) qa21210000 (if_then_else_M (EQ_M (to x6) (i 2)) qa12210000 (if_then_else_M (EQ_M (to x6) (i 4)) qa11220000 O))).
Definition qa11200001_s := (if_then_else_M (EQ_M (to x6) (i 1))  qa21200001 (if_then_else_M (EQ_M (to x6) (i 2))  qa12200001 O)).

(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000-> qa11110000->******************)


Definition qa11120000_s := (if_then_else_M (EQ_M (to x6) (i 1))  qa21120000 (if_then_else_M (EQ_M (to x6) (i 2))  qa12120000 (if_then_else_M (EQ_M (to x6) (i 3))  qa11220000 O))).
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000->qa11100001->******************)

(*************///qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 ->/// ****************)
(*************qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 -> qa11010010-> ****************)

Definition qa11020010_s := (if_then_else_M (EQ_M (to x6) (i 1))  qa21020010 (if_then_else_M (EQ_M (to x6) (i 2))  qa12020010 O))  .






(*****************end qa11000000 **********************************************)

(****************start qa10000100 ********************************************)
(********/// qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->///  *)
(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->  qa10200100-> *)

Definition  qa10210100_s := (if_then_else_M (EQ_M (to x6) (i 1))  qa20210100 (if_then_else_M (EQ_M (to x6) (i 4))  qa10220100 O)).
Definition   qa10200101_s :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa20200101 O).
(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->   qa10110100-> *)
(*Definition qa20110100_s :=  (if_then_else_M (EQ_M (to x6) (i 3))  qa20210100 (if_then_else_M (EQ_M (to x6) (i 4)) O  O)).
*)
Definition  qa10120100_s := (if_then_else_M (EQ_M (to x6) (i 1))  qa20120100 (if_then_else_M (EQ_M (to x6) (i 3))  qa10220100 O)).


(*************** /// qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 ->///*********)
(***************  qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 -> qa10010110 -> *********)


(*Definition qa20010110  := O.*)
Definition qa10020110_s  :=   (if_then_else_M (EQ_M (to x6) (i 1)) qa20020110 O).
(***************  qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 -> qa10000111  -> *********)

(*Definition qa20000111  := O. *)
(******************************/// qa00000000 ->  qa10000000 -> qa10000100 -> qa10010100->///************)
(****************************** qa00000000 ->  qa10000000 -> qa10000100 -> qa10010100-> qa10020100 ->*************************)




(******************end   qa10000100 ***********************)

(*****************************start qa10100000 **********)

(******** ///qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 ->///   *)
(******** qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 -> qa10210000->  *)

Definition qa10220000_s := (if_then_else_M (EQ_M (to x6) (i 1)) qa20220000 O).


(******************///qa00000000 -> qa10000000 -> qa10100000 -> qa10110000->///*)
(******************qa00000000 -> qa10000000 -> qa10100000 -> qa10110000->  qa10120000 ->*)

(*Definition qa20120000 := O.*)
(*Definition qa10220000 := O.*)
(*Definition qa11120000 := O.*)
(*Definition qa10120100 := O.*)



(*****************************end qa10100000 **********)


(*****************************start qa10000010 **********)
(********/// qa00000000 -> qa10000000 -> qa10000010 -> qa10010010 ->///  *)

(******** qa00000000 -> qa10000000 -> qa10000010 -> qa10010010 -> qa10020010  ->  *)



(*Definition qa20020010  := O.*)
(*Definition qa11020010  := O.*)
(*Definition qa10020110 := O.*)





(*****************************end qa10000010 **********)

(*****************************start qa10010000 **********)



(*****************************end qa10010000 **********)


(*****************************start qa10000001 **********)




(********************end qa10000001 **********************************)


(************/// end qa10000000/// ***************)

(**********************************************************************************************)

(************/// start qa00001000/// ***************)

(****************************start qa01001000 **********)
(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 ->/// *)
(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> qa02101000 -> *)
 
Definition qa02201000_s :=   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02211000 (if_then_else_M (EQ_M (to x6) (i 4)) qa02201001 O) ).
Definition qa02111000_s :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa02211000  (if_then_else_M (EQ_M (to x6) (i 1)) qa02121000 O)).
(*Definition qa02101001 :=  (if_then_else_M (EQ_M (to x6) (i 3)) acc O).*)
(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 ->  qa02001010 -> *)
Definition qa02011010_s := (if_then_else_M (EQ_M (to x6) (i 4)) qa02021010 O).
Definition  qa02001011_s := O.

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 ->  qa02011000-> *)
Definition qa02021000_s := (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa02121000 (if_then_else_M (EQ_M (to x6) (i 3)) qa02021010 O) ).

(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->/// *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->  qa01201000 -> *)

(*Definition  qa02201000 := O.*)
Definition  qa01211000_s :=    (if_then_else_M (EQ_M (to x6) (i 2)) qa02211000  (if_then_else_M (EQ_M (to x6) (i 4)) qa01221000 O)).

Definition  qa01201001_s :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02201001 O).

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 ->  qa01111000  -> *)

Definition qa01121000_s :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02121000 (if_then_else_M (EQ_M (to x6) (i 3)) qa01221000 O)).

(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 ->/// *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 ->  qa01011010 -> *)

  (*Definition qa02011010:= (if_then_else_M (EQ_M (to x6) (i 2)) acc O).*)
Definition qa01021010_s := (if_then_else_M (EQ_M (to x6) (i 2)) qa02021010  O).


(***///qa00000000 -> qa00001000 ->  qa01001000 ->  qa01011000 ->/// *)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01011000 -> qa01021000 -> *)


(***///qa00000000 -> qa00001000 ->  qa01001000 ->   qa01001001->/// *)
(***qa00000000 -> qa00001000 ->  qa01001000 ->   qa01001001-> *)

(****************************end qa01001000 **********)

(*************************start qa00001100 ************)
(***///qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> /// *)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> qa00201100 -> *)
Definition qa00211100_s := (if_then_else_M (EQ_M (to x6) (i 4))  qa00221100 O).
Definition qa00201101_s :=  O.
 
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 ->   qa00111100  -> *)
(*Definition  qa00211100 := O.*)
Definition  qa00121100_s := (if_then_else_M (EQ_M (to x6) (i 3)) qa00221100 O).

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> qa00101101   -> *)
(*Definition qa00201101 := O.*)
(**///*qa00000000 -> qa00001000 ->  qa00001100 -> qa00001110 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001110 -> qa00011110 -> *)

Definition qa00021110_s := O.

 
(***///qa00000000 -> qa00001000 ->  qa00001100 -> qa00011100 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00011100 -> qa00021100 -> *)


(***///qa00000000 -> qa00001000 ->  qa00001100 -> qa00001101 ->/// *)

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001101 -> *)


(************** end qa00001100 ************)
(*************************start  qa00101000 ************)
(***///qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 ->qa00211000 -> *)
Definition qa00221000_s :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01221000 (if_then_else_M (EQ_M (to x6) (i 2)) qa00221100 O)).

(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 -> qa00201001 -> *)

(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 -> qa00201001 -> *)


(***///qa00000000 -> qa00001000 ->  qa00101000 -> qa00111000 -> ///*)

(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00111000 ->qa00121000 -> *)


(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00101001 -> *)


(*************************end  qa00101000 ********)
(*********************start qa00001010 ************)

(***///qa00000000 -> qa00001000 ->  qa00001010 ->  qa00011010 ->/// *)
(***qa00000000 -> qa00001000 ->  qa00001010 ->  qa00011010 ->  qa00021010 -> *)




(***********end qa00001010 ************)
(***********************start qa00011000 ****)


(***********************end qa00011000 ****)
(*********commented out qa00001001**********)

(************/// end qa00001000/// ***************)

(************/// start qa01000000/// ***************)

(******* start qa02000000 ************)
(***///qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> ///*)
(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> qa02200000 -> *)


Definition qa02210000_s :=  (if_then_else_M (EQ_M (to x6) (i 4))  qa02220000  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa12210000 (if_then_else_M (EQ_M (to x6) (i 1))  qa02211000 O))).

(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 ->  qa02110000 -> *)
(*Definition qa02210000 := O.*)
Definition qa02120000_s :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa02220000  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12120000 (if_then_else_M (EQ_M (to x6) (i 1)) qa02121000 O))).

(***///qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 ->/// *)
(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 -> qa02010010 -> *)

Definition qa02020010_s :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa12020010 (if_then_else_M (EQ_M (to x6) (i 1))  qa02021010 O)).

(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 ->  qa02000011 -> *)


(***///qa00000000 ->  qa01000000 ->  qa02000000 ->qa02010000 -> ///*)
(***qa00000000 ->  qa01000000 ->  qa02000000 ->qa02010000 -> qa02020000 -> *)


(******* end qa02000000 ************)
(******* start qa01100000 ************)
(*///qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->///*)
(*qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->qa01210000 -> *)

Definition qa01220000_s :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02220000 (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11220000 (if_then_else_M (EQ_M (to x6) (i 1)) qa01221000 O))).


(*qa00000000 -> qa01000000 -> qa01100000 -> qa01200000-> qa01200001 -> *)


(*///qa00000000 -> qa01000000 -> qa01100000 ->  qa01110000 ->///*)
(*qa00000000 -> qa01000000 -> qa01100000 ->  qa01110000 -> qa01120000 ->*)


(******* end qa01100000 ************)
(******* start qa01000010************)
(*///qa00000000 -> qa01000000 ->qa01000010 -> qa01010010 ->/// **)
(*qa00000000 -> qa01000000 ->qa01000010 -> qa01010010 -> qa01020010 -> **)



(******* end qa01000010************)

(**********qa01000001 commented out***********)
(************/// end qa01000000/// ***************)
(************/// start qa00000100/// ***************)
(*******start qa00000110************)
(*///qa00000000 -> qa00000100 ->  qa00000110 -> qa00010110 ->/// **)
(*qa00000000 -> qa00000100 ->  qa00000110 -> qa00010110 -> qa00020110 -> **)





(*******end qa00000110************)
(*********start qa00010100 ****************************)
(*///qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 ->/// **)
(*qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 -> qa00120100 -> **)

Definition qa00220100_s :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10220100(if_then_else_M (EQ_M (to x6) (i 1)) qa00221100 O)).



(*********end qa00010100 ****************************)
(********start qa00000101 **************************)
(*///qa00000000 -> qa00000100 ->  qa00000101-> qa00100101 ->/// **)
(*qa00000000 -> qa00000100 ->  qa00000101-> qa00100101 -> qa00200101 -> **)



(********end qa00000101 **************************)


(************/// end qa00000100/// ***************)

(************/// start qa00100000/// ***************)
(******* start qa00200000************)



(*///qa00000000 ->  qa00100000  -> qa00200000 -> qa00210000 -> ///**)
(*qa00000000 ->  qa00100000  -> qa00200000 -> qa00210000 -> qa00220000 -> **)


(*****start qa00100001**********************)



(*****end qa00100001**********************)

(************/// end qa00000010/// ***************)


(************/// start qa00010000/// ***************)
(**********************start qa00020000 ****************)


(**********************stop qa00020000 ****************)
(************/// end qa00010000/// ***************)


(************/// start qa00000001/// ***************)
(*********start  qa10000001  ***********************)
(*qa00000000 ->  qa00000001 -> qa10000001 ->  qa10100001  ->*)


(********end qa10000001 ***************************)
(************/// end qa00000001/// ***************)
(*****************_s ing*******************************)

(************/// start qa10000000/// ***************)

(********************************start qa20000000******************************)

(******** qa00000000 -> qa10000000 -> qa20000000 ->  qa21000000 -> *********)
(** qa22000000  qa21100000  qa21000010  qa21010000 qa21000001 *)

Definition qa22000000_ss :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa22100000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa22000010_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa22010000_s (if_then_else_M (EQ_M (to x6) (i 4)) qa22000001_s O) ))).


Definition qa21100000_ss := (if_then_else_M (EQ_M (to x6) (i 2))  qa22100000_s (if_then_else_M (EQ_M (to x6) (i 3))  qa21200000_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa21110000_s (if_then_else_M (EQ_M (to x6) (i 4)) qa21100001_s O) ))).

Definition   qa21000010_ss := (if_then_else_M (EQ_M (to x6) (i 2))  qa22000010_s   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa21010010_s (if_then_else_M (EQ_M (to x6) (i 4)) qa21000011_s O) )).

Definition  qa21010000_ss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa22010000_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa21020000_s   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa21110000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa21010010_s O) ))).

Definition  qa21000001_ss := (if_then_else_M (EQ_M (to x6) (i 2)) qa22000001_s   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa21100001_s (if_then_else_M (EQ_M (to x6) (i 3)) qa21000011_s O) )).


(*********qa00000000 -> qa10000000 -> qa20000000 -> qa20000100 ->*****************************************)
(** qa20100100  qa20000110  qa20010100  qa20000101*)

Definition qa20100100_ss  :=  (if_then_else_M (EQ_M (to x6) (i 3))   qa20200100_s    (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa20110100_s (if_then_else_M (EQ_M (to x6) (i 4)) qa20100101_s O) )).

Definition  qa20000110_ss :=     (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  (*qa20010110_s*) O (if_then_else_M (EQ_M (to x6) (i 4)) qa20000111_s O) ).
Definition  qa20010100_ss  :=   (if_then_else_M (EQ_M (to x6) (i 4))  qa20020100_s (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa20110100_s (if_then_else_M (EQ_M (to x6) (i 3)) (*qa20010110_s*) O O) )).
Definition  qa20000101_ss :=      (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20100101_s (if_then_else_M (EQ_M (to x6) (i 3)) qa20000111_s O) ).

(****qa00000000 -> qa10000000 -> qa20000000 ->qa20100000 ->*************)
(**qa20200000 qa21100000 qa20100100  qa20110000 qa20100001*)
Definition qa20200000_ss :=(if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21200000_s (if_then_else_M (EQ_M (to x6) (i 2))  qa20200100_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa20210000_s (if_then_else_M (EQ_M (to x6) (i 4))  qa20200001_s O) ))).

Definition   qa20110000_ss :=(if_then_else_M (EQ_M (to x6) (i 3))  qa20210000_s (if_then_else_M (EQ_M (to x6) (i 4)) qa20120000_s (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21110000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa20110100_s O) ))).

Definition  qa20100001_ss := (if_then_else_M (EQ_M (to x6) (i 3))  qa20200001_s (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21100001_s (if_then_else_M (EQ_M (to x6) (i 2))  qa20100101_s O) )).

(************************qa00000000 -> qa10000000 -> qa20000000 ->qa20000010 ->*************)
(***qa21000010 qa20000110 qa20010010 qa20000011****************************************************)

Definition  qa20010010_ss := (if_then_else_M (EQ_M (to x6) (i 4)) qa20020010_s (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21010010_s (if_then_else_M (EQ_M (to x6) (i 2)) (*qa20010110_s*) O O) )).
Definition  qa20000011_ss :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21000011_s (if_then_else_M (EQ_M (to x6) (i 2)) qa20000111_s O) ).

(*******************qa00000000 -> qa10000000 -> qa20000000 ->qa20010000->******************)
(**qa20020000 qa21010000 qa20010100 qa20110000 qa20010010 **************)
Definition qa20020000_ss :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21020000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa20020100_s (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20120000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa20020010_s O) )) ).



(**************qa00000000 -> qa10000000 -> qa20000000 -> qa20000001-> ***************************************)
(**  qa21000001  qa20000101  qa20100001  qa20000011*********)


(***********************end  qa20000000********************************)


(*************************start  qa11000000 **************************)

(******** qa00000000 -> qa10000000 -> qa11000000 -> qa12000000 -> *)

(** qa22000000 qa12100000 qa12000010 qa12010000 qa12000001 *)

Definition  qa12100000_ss :=
 (if_then_else_M (EQ_M (to x6) (i 1))   qa22100000_s (if_then_else_M (EQ_M (to x6) (i 3))  qa12200000_s   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa12110000_s (if_then_else_M (EQ_M (to x6) (i 4))  qa12100001_s O) )) ).
Definition  qa12000010_ss :=    (if_then_else_M (EQ_M (to x6) (i 1))  qa22000010_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa12010010_s (if_then_else_M (EQ_M (to x6) (i 4)) qa12000011_s O) )) .
Definition  qa12010000_ss :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa22010000_s (if_then_else_M (EQ_M (to x6) (i 4))  qa12020000_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa12110000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa12010010_s O) )) ).
Definition  qa12000001_ss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa22000001_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa12100001_s (if_then_else_M (EQ_M (to x6) (i 4)) qa12000011_s O) ) ).
(***qa00000000 -> qa10000000 -> qa11000000 ->qa11100000->******************)


Definition  qa11200000_ss := (if_then_else_M (EQ_M (to x6) (i 1)) qa21200000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa12200000_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa11210000_s (if_then_else_M (EQ_M (to x6) (i 4))  qa11200001_s O) )) ).
Definition  qa11110000_ss :=(if_then_else_M (EQ_M (to x6) (i 1)) qa21110000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa12110000_s  (if_then_else_M (EQ_M (to x6) (i 3)) qa11210000_s (if_then_else_M (EQ_M (to x6) (i 4))  qa11120000_s  O) )) ).
Definition  qa11100001_ss := (if_then_else_M (EQ_M (to x6) (i 1)) qa21100001_s (if_then_else_M (EQ_M (to x6) (i 2)) qa12100001_s  (if_then_else_M (EQ_M (to x6) (i 3))  qa11200001_s O ))).
(*************qa00000000 -> qa10000000 -> qa11000000 -> qa11000010 -> ****************)

Definition   qa11010010_ss := (if_then_else_M (EQ_M (to x6) (i 1))  qa21010010_s (if_then_else_M (EQ_M (to x6) (i 2)) qa12010010_s (if_then_else_M (EQ_M (to x6) (i 4)) qa11020010_s   O) ) ).

Definition   qa11000011_ss :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa21000011_s (if_then_else_M (EQ_M (to x6) (i 2)) qa12000011_s    O) ).

(**************qa00000000 -> qa10000000 -> qa11000000 ->qa11010000-> ***********)
(*qa21010000 qa12010000 qa11020000 qa11110000 qa11010010*)

Definition  qa11020000_ss := (if_then_else_M (EQ_M (to x6) (i 1)) qa21020000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa12020000_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa11120000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa11020010_s O ) ))).


(****************************************qa00000000 -> qa10000000 -> qa11000000 -> qa11000001-> *)
(****qa21000001 qa12000001 qa11100001 qa11000011 *)


(*****************end qa11000000 **********************************************)

(****************start qa10000100 ********************************************)

(******** qa00000000 ->  qa10000000 -> qa10000100 -> qa10100100 ->  *)
(**  qa20100100  qa10200100   qa10110100  qa10100101 *)

Definition   qa10200100_ss :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa20200100_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10210100_s (if_then_else_M (EQ_M (to x6) (i 4)) qa10200101_s O) ) ).
Definition    qa10110100_ss :=   (if_then_else_M (EQ_M (to x6) (i 1)) qa20110100_s (if_then_else_M (EQ_M (to x6) (i 3)) qa10210100_s   (if_then_else_M (EQ_M (to x6) (i 4)) qa10120100_s   O) ) ).
Definition  qa10100101_ss :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa20100101_s (if_then_else_M (EQ_M (to x6) (i 3)) qa10200101_s   O) ).



(***************  qa00000000 ->  qa10000000 -> qa10000100 -> qa10000110 ->*********)

(****  qa20000110  qa10010110  qa10000111   *)

Definition  qa10010110_ss  := (if_then_else_M (EQ_M (to x6) (i 1)) qa20010110 (if_then_else_M (EQ_M (to x6) (i 4)) qa10020110_s   O) ).
Definition  qa10000111_ss  := (if_then_else_M (EQ_M (to x6) (i 1)) qa20000111_s  O) .
(****************************** qa00000000 ->  qa10000000 -> qa10000100 -> qa10010100->*************************)
(* qa20010100  qa10020100  qa10110100  qa10010110  *)
(*Definition   qa20010100 := O. *)
Definition  qa10020100_ss :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa20020100_s  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa10120100_s (if_then_else_M (EQ_M (to x6) (i 3)) qa10020110_s O) ) ).


(*** qa00000000 ->  qa10000000 -> qa10000100 ->qa10000101->*****)

(*qa20000101 qa10100101 qa10000111 *)


(******************end   qa10000100 ***********************)

(*****************************start qa10100000 **********)


(******** qa00000000 -> qa10000000 -> qa10100000 -> qa10200000 ->   *)

(**  qa20200000 qa11200000 qa10200100 qa10210000 qa10200001 *)

Definition  qa10210000_ss := (if_then_else_M (EQ_M (to x6) (i 1)) qa20210000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa10220000_s   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11210000_s (if_then_else_M (EQ_M (to x6) (i 2))  qa10210100_s O) ) )).
Definition  qa10200001_ss := (if_then_else_M (EQ_M (to x6) (i 1)) qa20200001_s   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11200001_s (if_then_else_M (EQ_M (to x6) (i 2)) qa10200101_s O) ) ).

(******************qa00000000 -> qa10000000 -> qa10100000 -> qa10110000->*)
(*  qa20110000  qa10210000  qa10120000  qa11110000  qa10110100*)

Definition   qa10120000_ss := (if_then_else_M (EQ_M (to x6) (i 1))  qa20120000_s (if_then_else_M (EQ_M (to x6) (i 3))  qa10220000_s   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11120000_s (if_then_else_M (EQ_M (to x6) (i 2))  qa10120100_s O) ) )).


(***qa00000000 -> qa10000000 -> qa10100000 ->qa10100001->***)

(***qa20100001 qa10200001 qa11100001 qa10100101 *)

(*****************************end qa10100000 **********)


(*****************************start qa10000010 **********)

(******** qa00000000 -> qa10000000 -> qa10000010 -> qa10010010 ->  *)


(** qa20010010 qa10020010 qa11010010 qa10010110 *)

(*Definition  qa20010010  := O. *)
Definition  qa10020010_ss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa20020010_s  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11020010_s (if_then_else_M (EQ_M (to x6) (i 2))  qa10020110_s O) ) ).



(*****************************end qa10010000 **********)


(*****************************start qa10000001 **********)




(********************end qa10000001 **********************************)


(************/// end qa10000000/// ***************)

(**********************************************************************************************)

(************/// start qa00001000/// ***************)

(****************************start qa01001000 **********)

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa02001000 -> *)
 
Definition qa02101000_ss :=   (if_then_else_M (EQ_M (to x6) (i 3))  qa02201000_s  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02111000_s (if_then_else_M (EQ_M (to x6) (i 4)) qa02101001_s O) ) ).
Definition  qa02001010_ss :=     (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02011010_s (if_then_else_M (EQ_M (to x6) (i 4))  qa02001011_s O) ) .
Definition qa02011000_ss := (if_then_else_M (EQ_M (to x6) (i 4)) qa02021000_s (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa02111000_s (if_then_else_M (EQ_M (to x6) (i 3))  qa02011010_s O)))  .
Definition qa02001001_ss := (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa02101001_s (if_then_else_M (EQ_M (to x6) (i 3)) qa02001011_s O) ) .

(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01101000 -> *)

Definition  qa01201000_ss := (if_then_else_M (EQ_M (to x6) (i 2))  qa02201000_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01211000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa01201001_s O)))  .
Definition  qa01111000_ss := (if_then_else_M (EQ_M (to x6) (i 1)) qa02111000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa01211000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa01121000_s  O)))  .
Definition  qa01101001_ss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa02101001_s (if_then_else_M (EQ_M (to x6) (i 2))  qa01201001_s O)).


(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01001010 -> *)

 Definition qa01011010_ss  := (if_then_else_M (EQ_M (to x6) (i 2)) qa02011010_s (if_then_else_M (EQ_M (to x6) (i 4)) qa01021010_s O))  .
Definition  qa01001011_ss := (if_then_else_M (EQ_M (to x6) (i 2)) qa02001011_s  O)  .


(***qa00000000 -> qa00001000 ->  qa01001000 ->  qa01011000 -> *)
(*
Definition qa02011000 :=  O. *)
Definition qa01021000_ss :=   (if_then_else_M (EQ_M (to x6) (i 2)) qa02021000_s (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01121000_s (if_then_else_M (EQ_M (to x6) (i 3)) qa01021010_s O)))  .

(***qa00000000 -> qa00001000 ->  qa01001000 ->   qa01001001-> *)

(****************************end qa01001000 **********)

(*************************start qa00001100 ************)
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00101100 -> *)

Definition qa00201100_ss  := (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00211100_s (if_then_else_M (EQ_M (to x6) (i 4)) qa00201101_s O)).
Definition qa00111100_ss :=  (if_then_else_M (EQ_M (to x6) (i 3))  qa00211100_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa00121100_s O)).
Definition qa00101101_ss :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa00201101_s O).
(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001110 -> *)

Definition qa00011110_ss :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00021110_s O).
Definition qa00001111_ss := O.

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00011100 -> *)

Definition   qa00021100_ss  := (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00121100_s (if_then_else_M (EQ_M (to x6) (i 3)) qa00021110_s O)).

(***qa00000000 -> qa00001000 ->  qa00001100 -> qa00001101 -> *)




(************** end qa00001100 ************)
(*************************start  qa00101000 ************)
(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00201000 -> *)

Definition qa00211000_ss := (if_then_else_M (EQ_M (to x6) (i 4)) qa00221000_s (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01211000_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa00211100_s O))).
Definition qa00201001_ss := (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01201001_s  (if_then_else_M (EQ_M (to x6) (i 2)) qa00201101_s O)).

(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00111000 -> *)
(*Definition qa00211000 := O.*)
Definition qa00121000_ss  := (if_then_else_M (EQ_M (to x6) (i 3))  qa00221000_s (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01121000_s (if_then_else_M (EQ_M (to x6) (i 2))  qa00121100_s O))).
(*
Definition qa01111000 := O. 
Definition qa00111100:=  O.*)

(***qa00000000 -> qa00001000 ->  qa00101000 -> qa00101001 -> *)


(*************************end  qa00101000 ********)
(*********************start qa00001010 ************)

(***qa00000000 -> qa00001000 ->  qa00001010 ->  qa00011010 -> *)


Definition  qa00021010_ss  :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01021010_s  (if_then_else_M (EQ_M (to x6) (i 3))  qa00021110_s  O)).

(***qa00000000 -> qa00001000 ->  qa00001010 ->  qa00001011 -> *)

 

(***********end qa00001010 ************)
(***********************start qa00011000 ****)

(***qa00000000 -> qa00001000 ->  qa00011000 -> qa00021000 -> *)

(***********************end qa00011000 ****)
(*********commented out qa00001001**********)

(************/// end qa00001000/// ***************)

(************/// start qa01000000/// ***************)

(******* start qa02000000 ************)

(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02100000 -> *)

Definition qa02200000_ss  := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12200000_s (if_then_else_M (EQ_M (to x6) (i 1)) qa02201000_s (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02210000_s (if_then_else_M (EQ_M (to x6) (i 4)) qa02200001_s O)))).
(*
Definition qa12100000   :=  (if_then_else_M (EQ_M (to x6) (i 1)) (grn 258) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 259) (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 260) (if_then_else_M (EQ_M (to x6) (i 4)) (grn 260)  O)))).
Definition qa02101000 := O. *)
Definition qa02110000_ss := (if_then_else_M (EQ_M (to x6) (i 3)) qa02210000_s  (if_then_else_M (EQ_M (to x6) (i 4)) qa02120000_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12110000_s (if_then_else_M (EQ_M (to x6) (i 1)) qa02111000_s O)))).
(*Definition qa02100001 := O. *)

(***qa00000000 ->  qa01000000 ->  qa02000000 -> qa02000010 -> *)

Definition qa02010010_ss :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa02020010_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12010010_s (if_then_else_M (EQ_M (to x6) (i 2)) qa02011010_s O))).
Definition qa02000011_ss :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12000011_s  (if_then_else_M (EQ_M (to x6) (i 1)) qa02001011_s O)).

(***qa00000000 ->  qa01000000 ->  qa02000000 ->qa02010000 -> *)
Definition qa02020000_ss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12020000_s (if_then_else_M (EQ_M (to x6) (i 1)) qa02021000_s (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa02120000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa02020010_s O)))).


(***qa00000000 ->  qa01000000 ->  qa02000000 ->qa02000001 -> *)

(******* end qa02000000 ************)
(******* start qa01100000 ************)
(*qa00000000 -> qa01000000 -> qa01100000 -> qa01200000->*)
(*Definition qa02200000 := O.
Definition qa11200000 := O. 
Definition qa01201000 := O. *)
Definition qa01210000_ss :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02210000_s (if_then_else_M (EQ_M (to x6) (i 4)) qa01220000_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11210000_s (if_then_else_M (EQ_M (to x6) (i 1)) qa01211000_s O)))).
Definition qa01200001_ss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02200001_s (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11200001_s (if_then_else_M (EQ_M (to x6) (i 1))  qa01201001_s O))).

(*qa00000000 -> qa01000000 -> qa01100000 ->  qa01110000 ->*)

Definition  qa01120000_ss := (if_then_else_M (EQ_M (to x6) (i 2))  qa02120000_s (if_then_else_M (EQ_M (to x6) (i 3))  qa01220000_s (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11120000_s (if_then_else_M (EQ_M (to x6) (i 1))  qa01121000_s O)))).

(*qa00000000 -> qa01000000 -> qa01100000 -> qa01100001 ->*)

(******* end qa01100000 ************)
(******* start qa01000010************)
(*qa00000000 -> qa01000000 ->qa01000010 -> qa01010010 -> **)

Definition qa01020010_ss := (if_then_else_M (EQ_M (to x6) (i 2)) qa02020010_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11020010_s (if_then_else_M (EQ_M (to x6) (i 1)) qa01021010_s O))).



(*qa00000000 -> qa01000000 ->qa01000010 ->  qa01000011-> **)
(*
Definition qa02000011 := O. 
Definition qa11000011 := O.
Definition qa01001011 := O.*)

(******* end qa01000010************)

(**********qa01000001 commented out***********)
(************/// end qa01000000/// ***************)
(************/// start qa00000100/// ***************)
(*******start qa00000110************)

(*qa00000000 -> qa00000100 ->  qa00000110 -> qa00010110 -> **)

Definition qa00020110_ss :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10020110_s (if_then_else_M (EQ_M (to x6) (i 1))  qa00021110_s   O)).


(*qa00000000 -> qa00000100 ->  qa00000110 -> qa00000111 -> **)

(*******end qa00000110************)
(*********start qa00010100 ****************************)

(*qa00000000 -> qa00000100 ->  qa00010100->  qa00020100 -> **)

Definition  qa00120100_ss :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa00220100_s (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10120100_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00121100_s O))).

(*qa00000000 -> qa00000100 ->  qa00010100->  qa00110100 -> **)

Definition qa00210100_ss := (if_then_else_M (EQ_M (to x6) (i 4)) qa00220100_s  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10210100_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00211100_s O))).

(*********end qa00010100 ****************************)
(********start qa00000101 **************************)
(*qa00000000 -> qa00000100 ->  qa00000101-> qa00100101 -> **)

Definition qa00200101_ss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10200101_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00201101_s O)).
(*Definition qa10100101:= O.
Definition qa00101101 := O.*)
(********end qa00000101 **************************)


(************/// end qa00000100/// ***************)

(************/// start qa00100000/// ***************)
(******* start qa00200000************)

(*qa00000000 ->  qa00100000  -> qa00200000 -> qa00200100 -> **)


(*qa00000000 ->  qa00100000  -> qa00200000 -> qa00210000 -> **)

Definition qa00220000_ss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10220000_s (if_then_else_M (EQ_M (to x6) (i 1)) qa00221000_s (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01220000_s (if_then_else_M (EQ_M (to x6) (i 2)) qa00220100_s O)))).

(*qa00000000 ->  qa00100000  -> qa00200000 ->  qa00200001 -> **)

(*******end  qa00200000***)
(*****qa00100100 *****commented out**********)

(**start qa00110000****************************)
(*qa00000000 ->  qa00100000  ->  qa00110000 ->qa00120000 ->*)

(**end qa00110000****************************)
(*****start qa00100001**********************)
(*qa00000000 ->  qa00100000  ->   qa00100001 ->qa02100001 ->*)

Definition qa02200001_ss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) (*qa12200001*) O (if_then_else_M (EQ_M (to x6) (i 1))  O (*qa02201001*) O)).
Definition qa12100001_ss := (if_then_else_M (EQ_M (to x6) (i 1))  (*qa22100001*) O (if_then_else_M (EQ_M (to x6) (i 3)) O (*qa12200001*) O)).
Definition qa02101001_ss :=  (if_then_else_M (EQ_M (to x6) (i 3)) (*qa02201001*) O  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa02101001_s O)). 

(*****end qa00100001**********************)

(************/// end qa00000010/// ***************)


(************/// start qa00010000/// ***************)
(**********************start qa00020000 ****************)
(*qa00000000 ->  qa00010000 -> qa00020000 ->qa01020000   ->*)


(**********************stop qa00020000 ****************)
(************/// end qa00010000/// ***************)


(************/// start qa00000001/// ***************)
(*********start  qa10000001  ***********************)
(*qa00000000 ->  qa00000001 -> qa10000001 ->  qa10100001  ->*)


(********end qa10000001 ***************************)
(************/// end qa00000001/// ***************)

 (*************qa00000000 -> qa10000000 -> qa20000000 -> *)

Definition qa21000000_sss :=   (if_then_else_M (EQ_M (to x6) (i 2))   qa22000000_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa21100000_ss (if_then_else_M (EQ_M (to x6) (i 3)) qa21000010_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa21010000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa21000001_ss O))))).

Definition qa20000100_sss :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20100100_ss (if_then_else_M (EQ_M (to x6) (i 3)) qa20000110_ss   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa20010100_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa20000101_ss O)))).


Definition qa20100000_sss := (if_then_else_M (EQ_M (to x6) (i 3))  qa20200000_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21100000_ss  (if_then_else_M (EQ_M (to x6) (i 2))  qa20100100_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa20110000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa20100001_ss O))))).

Definition qa20000010_sss :=    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa21000010_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa20000110_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa20010010_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa20000011_ss O)))).
Definition qa20010000_sss := (if_then_else_M (EQ_M (to x6) (i 4)) qa20020000_ss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21010000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa20010100_ss   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20110000_ss (if_then_else_M (EQ_M (to x6) (i 3)) qa20010010_ss   O))))).

Definition qa20000001_sss :=    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21000001_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa20000101_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20100001_ss  (if_then_else_M (EQ_M (to x6) (i 3))  qa20000011_ss O)))).

(*******************************qa00000000 -> qa10000000 ->qa11000000 ->*******************)
(**
Definition qa21000000:=  (if_then_else_M (EQ_M (to x6) (i 1))  acc (if_then_else_M (EQ_M (to x6) (i 2))  acc   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 97) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 97)   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 98)  (if_then_else_M (EQ_M (to x6) (i 4)) (grn 98) O)))))).

qa12000000, qa11100000, qa11000010, qa11010000,qa11000001*)
Definition qa12000000_sss := (if_then_else_M (EQ_M (to x6) (i 1)) qa22000000_ss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa12100000_ss  (if_then_else_M (EQ_M (to x6) (i 3))  qa12000010_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa12010000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa12000001_ss O))))).


Definition  qa11100000_sss :=  (if_then_else_M (EQ_M (to x6) (i 1)) qa21100000_ss (if_then_else_M (EQ_M (to x6) (i 2))  qa12100000_ss  (if_then_else_M (EQ_M (to x6) (i 3))  qa11200000_ss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa11110000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa11100001_ss O))))).

Definition  qa11000010_sss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa21000010_ss  (if_then_else_M (EQ_M (to x6) (i 2))   qa12000010_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa11010010_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa11000011_ss O)))).
Definition qa11010000_sss :=   (if_then_else_M (EQ_M (to x6) (i 1)) qa21010000_ss (if_then_else_M (EQ_M (to x6) (i 2)) qa12010000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa11020000_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa11110000_ss  (if_then_else_M (EQ_M (to x6) (i 3))  qa11010010_ss O))))).
(*
Definition qa20000001:=    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) (grn 102)  (if_then_else_M (EQ_M (to x6) (i 2)) (grn 102)  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 103)  (if_then_else_M (EQ_M (to x6) (i 3)) (grn 103) O)))).
*)

(************************qa00000000 -> qa10000000 -> qa10000100 ->***************************)

(*******************qa20000100, qa10100100, qa10000110, qa10010100, qa10000101*****************************)
(*
Definition qa20000100 := (if_then_else_M (EQ_M (to x6) (i 1))  acc    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) (grn 36)  (if_then_else_M (EQ_M (to x6) (i 2)) (grn 36)  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 37)  (if_then_else_M (EQ_M (to x6) (i 3)) (grn 37) O))))).
*)
Definition qa10100100_sss := (if_then_else_M (EQ_M (to x6) (i 1))   qa20100100_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa10200100_ss     (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10110100_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa10100101_ss O)))).


Definition qa10000110_sss :=   (if_then_else_M (EQ_M (to x6) (i 1))   qa20000110_ss     (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa10010110_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa10000111_ss O))).

Definition  qa10010100_sss :=   (if_then_else_M (EQ_M (to x6) (i 1))  qa20010100_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa10020100_ss   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10110100_ss   (if_then_else_M (EQ_M (to x6) (i 3)) qa10010110_ss O)))).
Definition qa10000101_sss :=   (if_then_else_M (EQ_M (to x6) (i 1))  qa20000101_ss     (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa10100101_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa10000111_ss O))).

(***************************qa00000000 -> qa10000000 ->qa10100000->************************************************)
(*qa20100000, qa10200000, qa11100000, qa10100100, qa10110000, qa10100001*********)
(*
Definition qa20100000 :=   (if_then_else_M (EQ_M (to x6) (i 3))  acc  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) (grn 106)  (if_then_else_M (EQ_M (to x6) (i 2)) (grn 106) (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 107)  (if_then_else_M (EQ_M (to x6) (i 4)) (grn 107) O))))).
*)

Definition qa10200000_sss :=(if_then_else_M (EQ_M (to x6) (i 1))  qa20200000_ss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11200000_ss  (if_then_else_M (EQ_M (to x6) (i 2))  qa10200100_ss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10210000_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa10200001_ss O))))).
(*
Definition  qa11100000 := (if_then_else_M (EQ_M (to x6) (i 3))  acc  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) (grn 106)  (if_then_else_M (EQ_M (to x6) (i 2)) (grn 106) (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 107)  (if_then_else_M (EQ_M (to x6) (i 4)) (grn 107) O))))).

Definition  qa10100100 := (if_then_else_M (EQ_M (to x6) (i 3))  acc  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) (grn 106)  (if_then_else_M (EQ_M (to x6) (i 2)) (grn 106) (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (grn 107)  (if_then_else_M (EQ_M (to x6) (i 4)) (grn 107) O))))).
*)
Definition  qa10110000_sss := (if_then_else_M (EQ_M (to x6) (i 1))  qa20110000_ss (if_then_else_M (EQ_M (to x6) (i 3)) qa10210000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa10120000_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11110000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa10110100_ss  O))))).

Definition  qa10100001_sss := (if_then_else_M (EQ_M (to x6) (i 1))  qa20100001_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa10200001_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11100001_ss  (if_then_else_M (EQ_M (to x6) (i 2))  qa10100101_ss O)))).


(*****************************************qa00000000 -> qa10000000 ->qa10000010 -> ******************************************************************)
(****qa20000010, qa11000010, qa10000110, qa10010010,qa10000011****)

Definition  qa10010010_sss := (if_then_else_M (EQ_M (to x6) (i 1))  qa20010010_ss (if_then_else_M (EQ_M (to x6) (i 4))  qa10020010_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11010010_ss  (if_then_else_M (EQ_M (to x6) (i 2))  qa10010110_ss O)))).

Definition qa10000011_sss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa20000011_ss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11000011_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa10000111_ss O))).

(**************qa00000000 -> qa10000000 -> qa10010000 ->****************)
(****qa20010000,qa10020000, qa11010000, qa10010100, qa10110000,qa10010010****)


Definition qa10020000_sss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa20020000_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11020000_ss  (if_then_else_M (EQ_M (to x6) (i 2))  qa10020100_ss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa10120000_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa10020010_ss O))))).




(************************qa00000000 -> qa10000000 -> qa10000001 -> ******************************)
(****** qa20000001,  qa11000001  qa10000101 qa10100001 qa10000011 **)

Definition   qa11000001_sss := (if_then_else_M (EQ_M (to x6) (i 1))   qa21000001_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa12000001_ss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa11100001_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa11000011_ss O)))).

(*************************qa00000000 -> qa00001000 -> qa01001000 ->******************************)
(*******qa01001000**************************************)
(*qa02001000 qa01101000 qa01001010 qa01011000 qa01001001 *)


Definition qa02001000_sss :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))   qa02101000_ss   (if_then_else_M (EQ_M (to x6) (i 3))  qa02001010_ss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa02011000_ss  (if_then_else_M (EQ_M (to x6) (i 4))  O O)))).

Definition  qa01101000_sss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02101000_ss  (if_then_else_M (EQ_M (to x6) (i 3))  qa01201000_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa01111000_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa01101001_ss O)))). 
Definition  qa01001010_sss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02001010_ss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa01011010_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01001011_ss O))). 
Definition  qa01011000_sss :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02011000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01021000_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa01111000_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa01011010_ss O)))). 
Definition  qa01001001_sss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02001001_ss    (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01101001_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa01001001_ss O))).



(*********** qa00000000 -> qa00001000 ->qa00001100 -> ****)
(*qa00101100 qa00001110 qa00011100 qa00001101 *************)


Definition qa00101100_sss := (if_then_else_M (EQ_M (to x6) (i 3))  qa00201100_ss   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00111100_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00101101_ss O))).
Definition   qa00001110_sss :=  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00011110_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa00001111_ss O)).
Definition  qa000011100_sss := (if_then_else_M (EQ_M (to x6) (i 4))  qa00021100_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00111100_ss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00111100_ss O))).

Definition  qa00001101_sss :=   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00101101_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00001111_ss O)).

(**** qa00000000 -> qa00001000 -> qa00101000 -> **************************)

(***qa00201000 qa01101000 qa00101100 qa00111000 qa00101001****)

Definition qa00201000_sss := (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01201000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00201100_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa00211000_ss (if_then_else_M (EQ_M (to x6) (i 4)) qa00201001_ss O)))).

Definition  qa00111000_sss :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa00211000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00121000_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01111000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00111100_ss O)))).
Definition  qa00101001_sss :=   (if_then_else_M (EQ_M (to x6) (i 3)) qa00201001_ss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01101001_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00101101_ss O))).

(***** qa00000000 -> qa00001000 -> qa00001010 ->********************************)
(*** qa01001010  qa00001110  qa00011010  qa00001011 *)

Definition  qa00011010_sss := (if_then_else_M (EQ_M (to x6) (i 4))  qa00021010_ss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01011010_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00011110_ss  O))).
Definition  qa00001011_sss  :=  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01001011_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00001111_ss O)).


(*********qa00000000 -> qa00001000 ->qa00011000 ->******************************)
(***qa00021000 qa01011000 qa00011100 qa00111000 qa00011010 *)

Definition qa00021000_sss := (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01021000_ss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00021100_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00121000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00021010_ss O)))).

(***********qa00000000 -> qa00001000 ->qa00001001->********************************)


(****************************qa00000000 -> qa01000000 -> qa02000000 ->*****************)
(**qa12000000, qa02001000, qa02100000, qa02000010, qa02010000, qa02000001************)

Definition  qa02100000_sss :=  (if_then_else_M (EQ_M (to x6) (i 3)) qa02200000_ss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa12100000_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa02101000_ss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02110000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa02100001_ss O))))).
Definition  qa02000010_sss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12000010_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa02001010_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa02010010_ss  (if_then_else_M (EQ_M (to x6) (i 4))  qa02000011_ss O)))).
Definition  qa02010000_sss :=  (if_then_else_M (EQ_M (to x6) (i 4))  qa02020000_ss (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))qa12010000_ss  (if_then_else_M (EQ_M (to x6) (i 1)) qa02011000_ss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa02110000_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa02010010_ss O))))).
Definition  qa02000001_sss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12000001_ss  (if_then_else_M (EQ_M (to x6) (i 1)) qa02001001_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa02100001_ss  (if_then_else_M (EQ_M (to x6) (i 3)) qa02000011_ss O)))).

(***************qa00000000 -> qa01000000 -> qa01100000 ->***********************)
(**qa02100000, qa01200000, qa11100000, qa01101000, qa01110000, qa01100001************)


Definition  qa01200000_sss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02200000_ss (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11200000_ss  (if_then_else_M (EQ_M (to x6) (i 1)) qa01201000_ss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01210000_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01200001_ss O))))).

Definition  qa01110000_sss :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02110000_ss (if_then_else_M (EQ_M (to x6) (i 3)) qa01210000_ss (if_then_else_M (EQ_M (to x6) (i 4)) qa01120000_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11110000_ss  (if_then_else_M (EQ_M (to x6) (i 1)) qa01111000_ss  O))))).


Definition  qa01100001_sss := (if_then_else_M (EQ_M (to x6) (i 2)) qa02100001_ss (if_then_else_M (EQ_M (to x6) (i 3)) qa01200001_ss   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11100001_ss  (if_then_else_M (EQ_M (to x6) (i 1)) qa01101001_ss  O)))).
 
(****************************qa00000000 -> qa01000000 ->qa01000010 ->**************************************)



Definition  qa01010010_sss :=  (if_then_else_M (EQ_M (to x6) (i 2)) qa02010010_ss (if_then_else_M (EQ_M (to x6) (i 4)) qa01020010_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11010010_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa01011010_ss  O)))).
Definition  qa01000011_sss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02000011_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11000011_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa01001011_ss   O))).


 (*****************///end qa01000000///**********************************************)
(***********************************************************************************)


(*****************///start qa00000100///**********************************************)
(***********************************************************************************)


 (*****************************qa00000000 -> qa00000100 -> qa00000110 ->********************************)

Definition  qa00010110_sss :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00020110_ss   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10010110_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa00011110_ss  O))).
Definition qa00000111_sss :=    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000111 (if_then_else_M (EQ_M (to x6) (i 1)) qa00001111  O)).
(************qa00000000 -> qa00000100 ->qa00010100 ->**************************)
(*qa00020100, qa10010100 , qa00011100 , qa00110100, qa00010110***)
Definition qa00020100_sss :=    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10020100_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa00021100_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa00120100_ss (if_then_else_M (EQ_M (to x6) (i 3)) qa00020110_ss  O)))).


Definition  qa00110100_sss :=  (if_then_else_M (EQ_M (to x6) (i 3))  qa00210100_ss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00120100_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10110100_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa00111100_ss  O)))).

(**********************qa00000000 -> qa00000100 -> qa00000101 ->**************************************************************)
(* qa10000101,  qa00001101 ,  qa00100101   qa00000111 *)

Definition   qa00100101_sss := (if_then_else_M (EQ_M (to x6) (i 3))  qa00200101_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10100101_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa00101101_ss O))).

(*****************///end qa00000100///**********************************************)
(***********************************************************************************)


(*****************///start  qa001000000 ///**********************************************)
(***********************************************************************************)
(************qa00000000 -> qa001000000 -> qa00200000 ->*)
(*qa10200000, qa00201000 , qa01200000, qa00200100,qa00210000, qa00200001*)

Definition  qa00200100_sss :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10200100_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa00201100_ss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00210100_ss (if_then_else_M (EQ_M (to x6) (i 4)) qa00200101_ss O)))).

Definition qa00210000_sss :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00220000_ss (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10210000_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa00211000_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa01210000_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa00210100_ss O))))).
Definition  qa00200001_sss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10200001_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa00201001_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01200001_ss (if_then_else_M (EQ_M (to x6) (i 2)) qa00200101_ss O)))).


(************qa00000000 -> qa00100000 -> qa00100100 ->***********************)
(* qa00200100, qa10100100, qa00101100, qa00110100 qa00100101 *)

(************qa00000000 -> qa001000000 -> qa00110000 ->*********************)
(*qa00210000 qa00120000 qa10110000 qa00111000 qa01110000 qa00110100*)

Definition  qa00120000_sss :=  (if_then_else_M (EQ_M (to x6) (i 3))  qa00220000_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10120000_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa00121000_ss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01120000_ss (if_then_else_M (EQ_M (to x6) (i 2)) qa00120100_ss O))))).

(****************qa00000000 -> qa00100000 -> qa00100001->******************************)
(*qa00200001 qa10100001 qa00101001 qa02100001 qa00100101*)


Definition  qa02100001_sss := (if_then_else_M (EQ_M (to x6) (i 3))  qa02200001_ss    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa12100001_ss (if_then_else_M (EQ_M (to x6) (i 1)) qa02101001_ss O))).


(*****************///end  qa00100000 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00000010 ///**********************************************)
(***********************************************************************************)
(*****************qa00000000 -> qa00000010 ->  qa00010010 ->**)
(** qa00020010  qa10010010  qa00011010  qa01010010  qa00010110**)
Definition  qa00020010_sss :=    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10020010_ss  (if_then_else_M (EQ_M (to x6) (i 1)) ( qa00021010_ss)  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa01020010_ss (if_then_else_M (EQ_M (to x6) (i 1))  qa00020110_ss O)))).

(***********qa00000000 -> qa00000010 ->qa00000011->***************************)

(**qa10000011 qa00001011 qa01000011 qa00000111**)

(*****************///end   qa00000010 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00010000 ///**********************************************)
(***********************************************************************************)
(**********qa00000000 -> qa00010000 -> qa00020000 -> ***)
(*qa10020000, qa00021000, qa01020000 , qa00020100 , qa00120000 qa00020010*)



Definition  qa01020000_sss  :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02020000_ss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11020000_ss (if_then_else_M (EQ_M (to x6) (i 1))  qa01021000_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa01120000_ss (if_then_else_M (EQ_M (to x6) (i 3))  qa01020010_ss O))))).

(**qa00000000 -> qa00010000 ->qa01010000 ->***)
(**qa02010000 qa01020000 qa11010000 qa01011000 qa01110000 qa01010010*)



(*****************///end  qa00010000 ///**********************************************)
(***********************************************************************************)


(*****************///start   qa00000001 ///**********************************************)
(***********************************************************************************)
(**********qa00000000 -> qa00000001 -> qa10000001 ->*)

(**qa20000001, qa11000001 , qa10000101 qa10010001 qa10000011 *)
(*Definition qa20000001 := O.
Definition  qa11000001 := O. 
 Definition  qa10000101 := O. *)
(*Definition  qa10100001_ss :=  (if_then_else_M (EQ_M (to x6) (i 1))  qa20100001  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa10200001 (if_then_else_M (EQ_M (to x6) (i 2)) (grn 165)  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) (grn 166) (if_then_else_M (EQ_M (to x6) (i 3)) (grn 166) O))))).*)
(**Definition  qa10000011 := O.**)

(***************qa00000000 -> qa00000001 -> qa00001001 ->**********)

(****qa01001001 qa00001101 qa00101001 qa00001011 *)
 (*Definition qa01001001 := O.*)
(*Definition  qa00001101 := O.*)
(*Definition  qa00101001 :=  O.*)
(*Definition qa00001011 := O.*)

(** qa00000000 -> qa00000001 -> qa01000001 ->*)

(*** qa02000001  qa11000001  qa01001001 qa01100001  qa01000011 ****)
(*Definition  qa02000001 := O.*)
(*Definition qa11000001 := O.*)
(*Definition qa01001001 := O. *)
(*Definition  qa01100001 := O.*)
(*Definition   qa01000011 :=  O. *)

(*****************///end  qa00000001 ///**********************************************)
(***********************************************************************************)

(**************************************************************************************************)
(**************************************************************************************************)



Definition qa20000000_ssss:=    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa21000000_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa20000100_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa20100000_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa20000010_sss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa20010000_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa20000001_sss O)))))).
Definition qa11000000_ssss := (if_then_else_M (EQ_M (to x6) (i 1))  qa21000000_sss (if_then_else_M (EQ_M (to x6) (i 2)) qa12000000_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa11100000_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa11000010_sss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa11010000_sss  (if_then_else_M (EQ_M (to x6) (i 4))  qa20000001_sss O)))))).
Definition qa10000100_ssss:= (if_then_else_M (EQ_M (to x6) (i 1))  qa20000100_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10100100_sss (if_then_else_M (EQ_M (to x6) (i 3)) qa10000110_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10010100_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa10000101_sss O))))).

Definition qa10100000_ssss:= (if_then_else_M (EQ_M (to x6) (i 1))  qa20100000_sss  (if_then_else_M (EQ_M (to x6) (i 3))   qa10200000_sss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11100000_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa10100100_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa10110000_sss   (if_then_else_M (EQ_M (to x6) (i 4)) qa10100001_sss O)))))).
Definition qa10000010_ssss := (if_then_else_M (EQ_M (to x6) (i 1))  qa20000010_sss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11000010_sss  (if_then_else_M (EQ_M (to x6) (i 2))  qa10000110_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))qa10010010_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa10000011_sss O))))).

Definition qa10010000_ssss:=  (if_then_else_M (EQ_M (to x6) (i 1)) qa20010000_sss  (if_then_else_M (EQ_M (to x6) (i 4))   qa10020000_sss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11010000_sss (if_then_else_M (EQ_M (to x6) (i 2))  qa10010100_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10110000_sss (if_then_else_M (EQ_M (to x6) (i 3))  qa10010010_sss  O)))))).

Definition qa10000001_ssss:= (if_then_else_M (EQ_M (to x6) (i 1)) qa20000001_sss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa11000001_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa10000101_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10100001_sss  (if_then_else_M (EQ_M (to x6) (i 3))  qa10000011_sss O))))).


(*******************qa00001000*******************************************************)


Definition qa01001000_ssss := (if_then_else_M (EQ_M (to x6) (i 2))  qa02001000_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa01101000_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa01001010_sss   (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01011000_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01001001_sss O))))).

Definition qa00001100_ssss := (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00101100_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00001110_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) (*qa00011100_ss*) O (if_then_else_M (EQ_M (to x6) (i 4))  qa00001101_sss O)))).

Definition qa00101000_ssss := (if_then_else_M (EQ_M (to x6) (i 3))   qa00201000_sss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01101000_sss  (if_then_else_M (EQ_M (to x6) (i 2)) 
qa00101100_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00111000_sss (if_then_else_M (EQ_M (to x6) (i 4))  qa00101001_sss O))))).


Definition qa00001010_ssss :=    (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))
 qa01001010_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00001110_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa00011010_sss  (if_then_else_M (EQ_M (to x6) (i 4))  qa00001011_sss O)))).

Definition qa00011000_ssss :=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00021000_sss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01011000_sss  (if_then_else_M (EQ_M (to x6) (i 2)) (*qa00011100_ss*) O  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00111000_sss (if_then_else_M (EQ_M (to x6) (i 3))  qa00011010_sss O))))).

Definition qa00001001_ssss :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01001001_sss  (if_then_else_M (EQ_M (to x6) (i 2))  qa00001101_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00101001_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00001011_sss O)))).


(**************************qa01000000*******************************************************)




Definition qa02000000_ssss := (if_then_else_M (EQ_M (to x6) (i 2)) qa12000000_sss   (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa02100000_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa02000010_sss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa02010000_sss  (if_then_else_M (EQ_M (to x6) (i 4))  qa02000001_sss O))))).


Definition qa01100000_ssss  :=    (if_then_else_M (EQ_M (to x6) (i 2))  qa02100000_sss  (if_then_else_M (EQ_M (to x6) (i 3))  qa01200000_sss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11100000_sss  (if_then_else_M (EQ_M (to x6) (i 1))  qa01101000_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01110000_sss  (if_then_else_M (EQ_M (to x6) (i 4))  qa01100001_sss O)))))).

Definition qa01000010_ssss :=  (if_then_else_M (EQ_M (to x6) (i 2))  qa02000010_sss   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11000010_sss  (if_then_else_M (EQ_M (to x6) (i 1))  qa01001010_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01010010_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01000011_sss O))))).

Definition qa01010000_ssss := (if_then_else_M (EQ_M (to x6) (i 2))  qa02010000_sss  (if_then_else_M (EQ_M (to x6) (i 4))  qa01020000_sss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11010000_sss  (if_then_else_M (EQ_M (to x6) (i 1)) qa01011000_sss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01110000_sss (if_then_else_M (EQ_M (to x6) (i 3)) qa01010010_sss O)))))).

Definition qa01000001_ssss:=  (if_then_else_M (EQ_M (to x6) (i 2))   qa02000001_sss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11000001_sss (if_then_else_M (EQ_M (to x6) (i 1)) qa01001001_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa01100001_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa01000011_sss O))))).


(**************************qa00000100*******************************************************)




Definition qa00000110_ssss :=    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10000110_sss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00001110_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00010110_sss  (if_then_else_M (EQ_M (to x6) (i 4))  qa00000111_sss O)))).

Definition qa00010100_ssss:=  (if_then_else_M (EQ_M (to x6) (i 4)) qa00020100_sss    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10010100_sss  (if_then_else_M (EQ_M (to x6) (i 1)) (*qa00011100_ss *) O  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa00110100_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00010110_sss O))))).

Definition qa00000101_ssss :=  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000101_sss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00001101_sss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00100101_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00000111_sss O)))).


(**************************qa001000000*******************************************************)

Definition qa00200000_ssss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10200000_sss  (if_then_else_M (EQ_M (to x6) (i 1)) qa00201000_sss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01200000_sss (if_then_else_M (EQ_M (to x6) (i 2)) qa00200100_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa00210000_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00200001_sss O)))))).


Definition qa00100100_ssss :=  (if_then_else_M (EQ_M (to x6) (i 3))  qa00200100_sss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10100100_sss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00101100_sss  (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00110100_sss  (if_then_else_M (EQ_M (to x6) (i 4))  qa00100101_sss O))))).

Definition qa00110000_ssss := (if_then_else_M (EQ_M (to x6) (i 3))  qa00210000_sss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00120000_sss    (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10110000_sss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00111000_sss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01110000_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00110100_sss O)))))).

Definition qa00100001_ssss := (if_then_else_M (EQ_M (to x6) (i 3)) qa00200001_sss   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10100001_sss  (if_then_else_M (EQ_M (to x6) (i 1)) qa00101001_sss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa02100001_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00100101_sss O))))).

(**************************qa00000010*******************************************************)



Definition qa00010010_ssss:=  (if_then_else_M (EQ_M (to x6) (i 4))  qa00020010_sss   (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa10010010_sss  (if_then_else_M (EQ_M (to x6) (i 1))  qa00011010_sss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01010010_sss (if_then_else_M (EQ_M (to x6) (i 2))  qa00010110_sss O))))).

Definition qa00000011_ssss :=  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa10000011_ss  (if_then_else_M (EQ_M (to x6) (i 2))  qa00001011_ss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01000011_ss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00000111_ss O)))).

(**************************qa00010000*******************************************************)




Definition qa00020000_ssss := (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10020000_sss (if_then_else_M (EQ_M (to x6) (i 1))  qa00021000_sss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01020000_sss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00020100_sss     (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00120000_sss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00020010_sss O)))))) .



(**************************qa00000001*******************************************************)










Definition qa10000000_sssss :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M (EQ_M (to x6) (i 1)) qa20000000_ssss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa11000000_ssss  (if_then_else_M (EQ_M (to x6) (i 2)) qa10000100_ssss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa10100000_ssss (if_then_else_M (EQ_M (to x6) (i 3)) qa10000010_ssss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa10010000_ssss (if_then_else_M (EQ_M (to x6) (i 4)) qa10000001_ssss O))))))))))).

Definition qa00001000_sssss :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) & (EQ_M (to x6) (i 1)) mx1rn2 (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01001000_ssss  (if_then_else_M (EQ_M (to x6) (i 2)) qa00001100_ssss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new))  qa00101000_ssss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00001010_ssss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00011000_ssss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00001001_ssss O)))))))))).


Definition qa01000000_sssss :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M (EQ_M (to x6) (i 2)) qa02000000_ssss (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new))  qa11000000_ssss  (if_then_else_M (EQ_M (to x6) (i 1))  qa01001000_ssss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa01100000_ssss  (if_then_else_M (EQ_M (to x6) (i 3)) qa01000010_ssss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa01010000_ssss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01000001_ssss O))))))))))).

 Definition qa0000100_sssss :=  (if_then_else_M (EQ_M (reveal x6) (i 2) ) & (EQ_M (to x6) (i 2)) mx1rn2 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01001000_ssss  (if_then_else_M (EQ_M (to x6) (i 2))  qa00001100_ssss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00101000_ssss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00001010_ssss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))   qa00011000_ssss (if_then_else_M (EQ_M (to x6) (i 4))  qa00001001_ssss O)))))))))).

 Definition qa00100000_sssss :=  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O  (if_then_else_M (EQ_M (to x6) (i 3)) qa02000000_ssss (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa11000000_ssss (if_then_else_M (EQ_M (to x6) (i 1))  qa01001000_ssss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01100000_ssss  (if_then_else_M (EQ_M (to x6) (i 2)) qa01000010_ssss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa01010000_ssss  (if_then_else_M (EQ_M (to x6) (i 4)) qa01000001_ssss O))))))))))).

Definition  qa00000010_sssss  :=   (if_then_else_M (EQ_M (reveal x6) (i 3) ) & (EQ_M (to x6) (i 3)) mx1rn2 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (reveal x6) (i 2) ) O   (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000100_ssss (if_then_else_M (EQ_M (to x6) (i 4)) qa00001100_ssss   (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa00101000_ssss  (if_then_else_M (EQ_M (to x6) (i 2))  qa00000110_ssss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new))  qa00010100_ssss  (if_then_else_M (EQ_M (to x6) (i 4)) qa00000101_ssss O)))))))))).

Definition  qa00010000_sssss  :=    (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O  (if_then_else_M (EQ_M (to x6) (i 4)) qa00200000_ssss  (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10100000_ssss  (if_then_else_M (EQ_M (to x6) (i 1)) qa00101000_ssss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new))  qa01100000_ssss  (if_then_else_M (EQ_M (to x6) (i 2))   qa00100100_ssss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00110000_ssss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00100001_ssss O))))))))))).
Definition  qa00000001_sssss := (if_then_else_M (EQ_M (reveal x6) (i 4) ) & (EQ_M (to x6) (i 4)) mx1rn2 (if_then_else_M (EQ_M (reveal x6) (i 1) ) O  (if_then_else_M (EQ_M (reveal x6) (i 2) ) O   (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000001_ssss  (if_then_else_M (EQ_M (to x6) (i 1)) qa00001001_ssss (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01000001_ssss (if_then_else_M (EQ_M (to x6) (i 2)) qa00000101_ssss  (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00100001_ssss  (if_then_else_M (EQ_M (to x6) (i 3)) qa00000011_ssss O)))))))))).



(********************************************************************)


Definition t18:=  msg  (if_then_else_M (EQ_M (reveal x6) (i 1) ) O (if_then_else_M (EQ_M (reveal x6) (i 2) ) O  (if_then_else_M (EQ_M (reveal x6) (i 3) ) O (if_then_else_M (EQ_M (reveal x6) (i 4) ) O (if_then_else_M ((EQ_M (to x6) (i 1)) & (EQ_M (act x6) new)) qa10000000_sssss (if_then_else_M (EQ_M (to x6) (i 1)) qa00001000_sssss  (if_then_else_M ((EQ_M (to x6) (i 2)) & (EQ_M (act x6) new)) qa01000000_sssss (if_then_else_M (EQ_M (to x6) (i 2)) qa00001000_sssss (if_then_else_M ((EQ_M (to x6) (i 3)) & (EQ_M (act x6) new)) qa00100000_ssss  (if_then_else_M (EQ_M (to x6) (i 3))  qa00000010_sssss (if_then_else_M ((EQ_M (to x6) (i 4)) & (EQ_M (act x6) new)) qa00010000_sssss  (if_then_else_M (EQ_M (to x6) (i 4))  qa00000001_sssss O)) ))) ) )))))).


Definition phi7:= phi6 ++ [t18]. 



(*********************@@@@phi8@@@@@@@@@@@**************************************)
(*******************************************************************************)
