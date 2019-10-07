Load "extra_theorems".
 
(***********i1, i2, r3, r4****************************************************)
(*****************Real or random Secrecy*****************************************)
(********************************************************************************)
(******protocol Pi1 :The oracle reveals the actual nonce *************)

(********************************************************************************)

(********************NSL Protocol *********************************************)
(* A -> B : {(A , Na) }^r1_pkb 
  B -> A : { ((Na , Nb), B)}^r2_pka
   A -> B : { Nb}^r3_pkb
*)

(*********************real or random secrecy of Na*************)



Definition phi0  := [ msg (pk (N 1)) ; msg (pk (N 2)); msg (N 1); msg (N 2)].
Definition mphi0 := (conv_mylist_listm phi0).
Definition x1 := (f mphi0).

(******start state****************)
Definition sr (n:nat) := (rs (N 1)).

 Notation "( x , y )" := (pair x y) (at level 0).

 
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0).

Check pk.
SearchAbout pk.
Definition qa00 := 
 (if_then_elsem_ (EQM (reveal x1) (i 1) ) O (if_then_elsem_ (EQM (reveal x1) (i 2) ) O
 (if_then_elsem_ ((EQM (to x1) (i 1)) & (EQM (act x1) new)) (enc  ((N 1) , (nonce (N 1)))  (pk (N 2)) (sr 1)) 
(if_then_elsem_ (EQM (to x1) (i 2))  (enc   (( pi2(dec x1 (sk (N 2)) ) , (nonce (N 2))) , (N 2))   (pk (pi1  (dec x1 (sk (N 2)) ))) (sr 2))   O)))).



(************************)
Definition t12:= msg qa00.
Definition phi1 := phi0 ++ [ t12 ].


(***********************************************************)

Definition mphi1 := (conv_mylist_listm phi1).
Definition x2 := (f mphi1).

Definition tta1 ( x2 x1 :message) (j :nat) := (EQM (reveal x2) (i j)) & (EQM (to x1) (i j)).
Definition tta2 (x3 x2 x1 :message) (j:nat) := (EQM (reveal x3) (i j)) & (EQM (to x2) (i j)) & (EQM (to x1) (i j))& (notb (EQM (act x2) new)) & (EQM (act x1) new).

(**********qa00 -> qa10, qa01*************************************************)


Definition qa10 :=  (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ (EQM (reveal x2) (i 2) ) O (if_then_elsem_ (EQM (to x2) (i 1))  (enc (pi2 (pi1 (dec x2 (sk (N 1))))) (pk (pi2 (dec x2 (sk (N 1))))) (sr 3)) (if_then_elsem_ (EQM (to x2) (i 2))  (enc   (( pi2(dec x2 (sk (N 2)) ) , (nonce (N 2))) , (N 2))   (pk (pi1  (dec x2 (sk (N 2)) ))) (sr 4)) O)))).

Definition qa01 := (if_then_elsem_ ((EQM (reveal x2) (i 2) ) & (EQM (to x1) (i 2))) (pi2 (dec x1 (sk (N 2))) ) (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ ((EQM (to x2) (i 1)) & (EQM (act x2) new)) (enc  ((N 1) , (nonce (N 1)))  (pk (N 2)) (sr 5)) O))).



Definition t13 :=  msg (if_then_elsem_ (EQM (reveal x1) (i 1) ) O (if_then_elsem_ (EQM (reveal x1) (i 2) ) O
 (if_then_elsem_ ((EQM (to x1) (i 1)) & (EQM (act x1) new)) qa10
(if_then_elsem_ (EQM (to x1) (i 2)) qa01   O)))).
Definition phi2:= phi1 ++ [t13].



(***************************************************************************)

Definition mphi2 := (conv_mylist_listm phi2).
Definition x3 := (f mphi2).


Definition qa20 :=  (if_then_elsem_ ((EQM (reveal  x3) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))  (pi1 (pi1 (dec x2 (sk (N 1)))))  (  (if_then_elsem_ (EQM (reveal x3) (i 2) ) O  (if_then_elsem_ (EQM (to  x3) (i 2))  (enc   (( pi2(dec x3 (sk (N 2)) ) , (nonce (N 2))) , (N 2))   (pk (pi1  (dec x3 (sk (N 2)) ))) (sr 6))   O)))).


Definition qa11 :=  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x1) (i 2))) (pi2  (dec x1 (sk (N 2))))  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x2) (i 2))) (pi2  (dec x2 (sk (N 2))))  (if_then_elsem_ (EQM (to  x3) (i 1)) (enc (pi2 (pi1 (dec x3 (sk (N 1))))) (pk (pi2 x3)) (sr 7))  O))).

Definition qa02 := (if_then_elsem_ (EQM (reveal x3) (i 1) ) O  (if_then_elsem_ (EQM (to x3 ) (i 1)) & (EQM (act x3) new) (enc  ((N 1) , (nonce (N 1)))  (pk (N 2)) (sr 8))   O)).

Definition qa10_s :=  (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ (EQM (reveal x2) (i 2) ) O (if_then_elsem_ (EQM (to x2) (i 1))  qa20 (if_then_elsem_ (EQM (to x2) (i 2)) qa11 O)))).
Definition qa01_s := (if_then_elsem_ ((EQM (reveal x2) (i 2) ) & (EQM (to x1) (i 2))) qa02 (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ ((EQM (to x2) (i 1)) & (EQM (act x2) new)) qa11 O))).


Definition t14 :=  msg (if_then_elsem_ (EQM (reveal x1) (i 1) ) O (if_then_elsem_ (EQM (reveal x1) (i 2) ) O
 (if_then_elsem_ ((EQM (to x1) (i 1)) & (EQM (act x1) new)) qa10_s
(if_then_elsem_ (EQM (to x1) (i 2)) qa01_s   O)))).

Definition phi3:= phi2 ++ [t14]. 
(***********************************************************************************************)

Definition mphi3 := (conv_mylist_listm phi3).
Definition x4 := (f mphi3).

(********************qa2000 ->qbar, qa3000, qa2100, qa2001,qbar****************************************************)

Definition qa30 := (if_then_elsem_ (EQM (reveal  x4) (i 2) ) O (if_then_elsem_ (EQM (to  x4) (i 2)) (enc   (( pi2(dec x4 (sk (N 2)) ) , (nonce (N 2))) , (N 2))   (pk (pi1  (dec x4 (sk (N 2)) ))) (sr 9))  O )).
  
Definition qa21 := (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x1) (i 2)))  (pi2  (dec x1 (sk (N 2))))    (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x2) (i 2)))   (pi2  (dec x2 (sk (N 2))))  (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x3) (i 2)))  (pi2  (dec x3 (sk (N 2))))
 (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))   (pi1 (pi1 (dec x2 (sk (N 1))))) 
                                                                                                                                                                                               (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new))  (pi1 (pi1 (dec x3 (sk (N 1))))) 
                                           (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x2) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x2) new))  (pi1 (pi1 (dec x3 (sk (N 1)))))  O)))))).
 

Definition qa12 := (if_then_elsem_ (EQM (reveal  x4) (i 1) ) O ( if_then_elsem_ (EQM (to x4) (i 1)) (enc (pi2 (pi1 (dec x4 (sk (N 1))))) (pk (pi2 x4)) (sr 10)) O)).


(*****************************qa1001 -> qa1002, qa2001***************************************************)
Definition qa20_s :=  (if_then_elsem_ ((EQM (reveal  x3) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))  qa30  (  (if_then_elsem_ (EQM (reveal x3) (i 2) ) O  (if_then_elsem_ (EQM (to  x3) (i 2))  qa21   O)))).


Definition qa11_s :=  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x1) (i 2))) qa12  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x2) (i 2))) qa12  (if_then_elsem_ (EQM (to  x3) (i 1)) qa21  O))).

Definition qa02_s := (if_then_elsem_ (EQM (reveal x3) (i 1) ) O  (if_then_elsem_ (EQM (to x3 ) (i 1)) & (EQM (act x3) new) qa12   O)).

Definition qa10_ss :=  (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ (EQM (reveal x2) (i 2) ) O (if_then_elsem_ (EQM (to x2) (i 1))  qa20_s (if_then_elsem_ (EQM (to x2) (i 2)) qa11_s O)))).
Definition qa01_ss := (if_then_elsem_ ((EQM (reveal x2) (i 2) ) & (EQM (to x1) (i 2))) qa02_s (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ ((EQM (to x2) (i 1)) & (EQM (act x2) new)) qa11_s O))).


Definition t15 :=  msg (if_then_elsem_ (EQM (reveal x1) (i 1) ) O (if_then_elsem_ (EQM (reveal x1) (i 2) ) O
 (if_then_elsem_ ((EQM (to x1) (i 1)) & (EQM (act x1) new)) qa10_ss
(if_then_elsem_ (EQM (to x1) (i 2)) qa01_ss  O)))).

Definition phi4:= phi3 ++ [t15]. 


(*******************************************phi5****************************************************************)
(***************************************************************************************************************)

Definition mphi4 := (conv_mylist_listm phi4).
Definition x5 := (f mphi4).

Definition qa31 := (if_then_elsem_ ((EQM (reveal  x5) (i 2) ) & (EQM (to x1) (i 2)))  (pi2  (dec x1 (sk (N 2))))    (if_then_elsem_ ((EQM (reveal  x5) (i 2) ) & (EQM (to x2) (i 2)))   (pi2  (dec x2 (sk (N 2))))  (if_then_elsem_ ((EQM (reveal  x5) (i 2) ) & (EQM (to x3) (i 2)))  (pi2  (dec x3 (sk (N 2)))) (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x4) (i 2)))  (pi2  (dec x4 (sk (N 2)))) O) ) ) ).   

Definition qa22 :=                                                                                                                                         (if_then_elsem_ ((EQM (reveal  x5) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))  (pi1 (pi1 (dec x2 (sk (N 1))))) 
                                           (if_then_elsem_ ((EQM (reveal  x5) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new))  (pi1 (pi1 (dec x3 (sk (N 1)))))  (if_then_elsem_ ((EQM (reveal  x5) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x2) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x2) new))  (pi1 (pi1 (dec x3 (sk (N 1)))))  (if_then_elsem_ ((EQM (reveal  x5) (i 1) ) & (EQM (to x4) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x4) new)) &(EQM (act x1) new))  (pi1 (pi1 (dec x4 (sk (N 1)))))  (if_then_elsem_ ((EQM (reveal  x5) (i 1) ) & (EQM (to x4) (i 1)) &(EQM (to x2) (i 1)) & (notb (EQM ( act x4) new)) &(EQM (act x2) new))  (pi1 (pi1 (dec x4 (sk (N 1))))) (if_then_elsem_ ((EQM (reveal  x5) (i 1) ) & (EQM (to x4) (i 1)) &(EQM (to x3) (i 1)) & (notb (EQM ( act x4) new)) &(EQM (act x3) new))  (pi1 (pi1 (dec x4 (sk (N 1))))) O ) ) )))).

(************************************************************************************)
Definition qa30_s := (if_then_elsem_ (EQM (reveal  x4) (i 2) ) O (if_then_elsem_ (EQM (to  x4) (i 2)) qa31  O )).
  
Definition qa21_s := (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x1) (i 2)))  qa22    (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x2) (i 2)))   qa22  (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x3) (i 2)))  qa22
 (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new)) qa22
                                                                                                                                                                                               (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new))  qa31
                                           (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x2) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x2) new))  qa31  O)))))).
 

Definition qa12_s := (if_then_elsem_ (EQM (reveal  x4) (i 1) ) O ( if_then_elsem_ (EQM (to x4) (i 1)) qa22 O)).


(*****************************qa1001 -> qa1002, qa2001***************************************************)
Definition qa20_ss :=  (if_then_elsem_ ((EQM (reveal  x3) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))  qa30_s  (  (if_then_elsem_ (EQM (reveal x3) (i 2) ) O  (if_then_elsem_ (EQM (to  x3) (i 2))  qa21_s   O)))).


Definition qa11_ss :=  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x1) (i 2))) qa12_s  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x2) (i 2))) qa12_s  (if_then_elsem_ (EQM (to  x3) (i 1)) qa21_s  O))).

Definition qa02_ss := (if_then_elsem_ (EQM (reveal x3) (i 1) ) O  (if_then_elsem_ (EQM (to x3 ) (i 1)) & (EQM (act x3) new) qa12_s   O)).
(****************************************************************************************************************)

Definition qa10_sss :=  (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ (EQM (reveal x2) (i 2) ) O (if_then_elsem_ (EQM (to x2) (i 1))  qa20_ss (if_then_elsem_ (EQM (to x2) (i 2)) qa11_ss O)))).
Definition qa01_sss := (if_then_elsem_ ((EQM (reveal x2) (i 2) ) & (EQM (to x1) (i 2))) qa02_ss (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ ((EQM (to x2) (i 1)) & (EQM (act x2) new)) qa11_ss O))).


Definition t16 :=  msg (if_then_elsem_ (EQM (reveal x1) (i 1) ) O (if_then_elsem_ (EQM (reveal x1) (i 2) ) O
 (if_then_elsem_ ((EQM (to x1) (i 1)) & (EQM (act x1) new)) qa10_sss
(if_then_elsem_ (EQM (to x1) (i 2)) qa01_sss  O)))).

Definition phi5:= phi4 ++ [t15]. 

(******************************************************************************************************************************************************)
(******************************************************************************************************************************************************)
(***********************protocol Pi2 : add transitions to qa2001************)
(***************************************************************************)



Definition phi21 := phi1.
Definition phi22 := phi2.
Definition phi23 := phi3.



Definition qb21 := (if_then_elsem_ (EQM (reveal  x4) (i 2) ) & (EQM (to  x3) (i 1)) &(EQM (to x2) (i 2))&(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new) & (EQM  (pi2  (dec x1 (sk (N 2)))) (N 1)) & (EQM  (pi2  (dec x2 (sk (N 2)))) (N 1)) & (EQM  (pi2  (dec x3 (sk (N 2)))) (N 1)) & (EQM  (pi1 (pi1 (dec x2 (sk (N 1)))))  (N 1)) & (EQM  (pi1 (pi1 (dec x3 (sk (N 1)))))  (N 1))  (N 3)  (if_then_elsem_ (EQM (reveal  x4) (i 1) ) & (EQM (to  x3) (i 1)) &(EQM (to x2) (i 2))&(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new) & (EQM  (pi2  (dec x1 (sk (N 2)))) (N 1)) & (EQM  (pi2  (dec x2 (sk (N 2)))) (N 1)) & (EQM  (pi2  (dec x3 (sk (N 2)))) (N 1)) & (EQM  (pi1 (pi1 (dec x2 (sk (N 1)))))  (N 1)) & (EQM  (pi1 (pi1 (dec x3 (sk (N 1)))))  (N 1))  (N 3) (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x1) (i 2)))  (pi2  (dec x1 (sk (N 2))))    (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x2) (i 2)))   (pi2  (dec x2 (sk (N 2))))  (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x3) (i 2)))  (pi2  (dec x3 (sk (N 2))))
 (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))   (pi1 (pi1 (dec x2 (sk (N 1))))) 
                                                                                                                                                                                               (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new))  (pi1 (pi1 (dec x3 (sk (N 1))))) 
                                           (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x2) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x2) new))  (pi1 (pi1 (dec x3 (sk (N 1)))))  O)))))))).




(********************************************************************************)

Definition qb20_s :=  (if_then_elsem_ ((EQM (reveal  x3) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))  qa30  (  (if_then_elsem_ (EQM (reveal x3) (i 2) ) O  (if_then_elsem_ (EQM (to  x3) (i 2))  qb21   O)))).


Definition qb11_s :=  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x1) (i 2))) qa12  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x2) (i 2))) qa12  (if_then_elsem_ (EQM (to  x3) (i 1)) qb21  O))).

Definition qb02_s := (if_then_elsem_ (EQM (reveal x3) (i 1) ) O  (if_then_elsem_ (EQM (to x3 ) (i 1)) & (EQM (act x3) new) qa12   O)).
(********************************************************************************)

Definition qb10_ss :=  (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ (EQM (reveal x2) (i 2) ) O (if_then_elsem_ (EQM (to x2) (i 1))  qb20_s (if_then_elsem_ (EQM (to x2) (i 2)) qb11_s O)))).
Definition qb01_ss := (if_then_elsem_ ((EQM (reveal x2) (i 2) ) & (EQM (to x1) (i 2))) qb02_s (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ ((EQM (to x2) (i 1)) & (EQM (act x2) new)) qb11_s O))).


Definition t25 :=  msg (if_then_elsem_ (EQM (reveal x1) (i 1) ) O (if_then_elsem_ (EQM (reveal x1) (i 2) ) O
 (if_then_elsem_ ((EQM (to x1) (i 1)) & (EQM (act x1) new)) qb10_ss
(if_then_elsem_ (EQM (to x1) (i 2)) qb01_ss  O)))).

Definition phi24:= phi3 ++ [t25]. 




(************************************************************************************)
(************************************************************************************)
(************************Protocol Pi2'': replace the output grn4 by mx12rn2 , mx13rn1 in the term qb2001 in Pi2**********)
(************************************************************************************************************************)



Definition phi31 := phi1.
Definition phi32 := phi2.
Definition phi33 := phi3.



Definition qc21 := (if_then_elsem_ (EQM (reveal  x4) (i 2) ) & (EQM (to  x3) (i 1)) &(EQM (to x2) (i 2))&(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new) & (EQM  (pi2  (dec x1 (sk (N 2)))) (N 1)) & (EQM  (pi2  (dec x2 (sk (N 2)))) (N 1)) & (EQM  (pi2  (dec x3 (sk (N 2)))) (N 1)) & (EQM  (pi1 (pi1 (dec x2 (sk (N 1)))))  (N 1)) & (EQM  (pi1 (pi1 (dec x3 (sk (N 1)))))  (N 1)) (pi2  (dec x2 (sk (N 2))))    (if_then_elsem_ (EQM (reveal  x4) (i 1) ) & (EQM (to  x3) (i 1)) &(EQM (to x2) (i 2))&(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new) & (EQM  (pi2  (dec x1 (sk (N 2)))) (N 1)) & (EQM  (pi2  (dec x2 (sk (N 2)))) (N 1)) & (EQM  (pi2  (dec x3 (sk (N 2)))) (N 1)) & (EQM  (pi1 (pi1 (dec x2 (sk (N 1)))))  (N 1)) & (EQM  (pi1 (pi1 (dec x3 (sk (N 1)))))  (N 1)) (pi1 (pi1 (dec x2 (sk (N 1))))) 

 (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x1) (i 2)))  (pi2  (dec x1 (sk (N 2))))    (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x2) (i 2)))   (pi2  (dec x2 (sk (N 2))))  (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x3) (i 2)))  (pi2  (dec x3 (sk (N 2))))
 (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))   (pi1 (pi1 (dec x2 (sk (N 1)))))                                                                                                                   (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new))  (pi1 (pi1 (dec x3 (sk (N 1))))) 
                                           (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x2) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x2) new))  (pi1 (pi1 (dec x3 (sk (N 1)))))  O)))))))).




(********************************************************************************)

Definition qc20_s :=  (if_then_elsem_ ((EQM (reveal  x3) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))  qa30  (  (if_then_elsem_ (EQM (reveal x3) (i 2) ) O  (if_then_elsem_ (EQM (to  x3) (i 2))  qc21   O)))).


Definition qc11_s :=  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x1) (i 2))) qa12  (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x2) (i 2))) qa12  (if_then_elsem_ (EQM (to  x3) (i 1)) qc21  O))).

Definition qc02_s := (if_then_elsem_ (EQM (reveal x3) (i 1) ) O  (if_then_elsem_ (EQM (to x3 ) (i 1)) & (EQM (act x3) new) qa12   O)).
(********************************************************************************)

Definition qc10_ss :=  (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ (EQM (reveal x2) (i 2) ) O (if_then_elsem_ (EQM (to x2) (i 1))  qc20_s (if_then_elsem_ (EQM (to x2) (i 2)) qc11_s O)))).
Definition qc01_ss := (if_then_elsem_ ((EQM (reveal x2) (i 2) ) & (EQM (to x1) (i 2))) qc02_s (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ ((EQM (to x2) (i 1)) & (EQM (act x2) new)) qc11_s O))).


Definition t35 :=  msg (if_then_elsem_ (EQM (reveal x1) (i 1) ) O (if_then_elsem_ (EQM (reveal x1) (i 2) ) O
 (if_then_elsem_ ((EQM (to x1) (i 1)) & (EQM (act x1) new)) qc10_ss
(if_then_elsem_ (EQM (to x1) (i 2)) qc01_ss  O)))).

Definition phi34:= phi3 ++ [t35]. 









(**************************


(******************************Protocol Pi2' : replace the output grn4 by grn21 in the term qb2001 in Pi2********)
(****************************************************************************************************************)

Definition phi41 := phi1.
Definition phi42 := phi2.
Definition phi43 := phi3.



Definition qd21 := (if_then_elsem_ (EQM (reveal  x4) (i 2) ) & (EQM (to  x3) (i 1)) &(EQM (to x2) (i 2))&(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new) &(EQM (m x2) (grn 1)) &(EQM (m  x3) (grn 2)) grn21 (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to  x3) (i 1)) &(EQM (to x2) (i 2))&(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new) &(EQM (m x2) (grn 1)) &(EQM (m  x3) (grn 2)))  grn21 (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x1) (i 2))) mx1rn1    (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x2) (i 2))) mx2rn2  (if_then_elsem_ ((EQM (reveal  x4) (i 2) ) & (EQM (to x3) (i 2))) mx3rn3
                                                                                                                                                                               (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new)) mx2rn1
                                                                                                                                                                                               (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x1) new)) mx3rn1
                                           (if_then_elsem_ ((EQM (reveal  x4) (i 1) ) & (EQM (to x3) (i 1)) &(EQM (to x2) (i 1)) & (notb (EQM ( act x3) new)) &(EQM (act x2) new)) mx3rn2 O))))))))   . 





(********************************************************************************)





Definition qd20_s :=  (if_then_elsem_ ((EQM (reveal  x3) (i 1) ) & (EQM (to x2) (i 1)) &(EQM (to x1) (i 1)) & (notb (EQM ( act x2) new)) &(EQM (act x1) new))  qa30  (if_then_elsem_ (EQM (reveal x3) (i 2) ) O (if_then_elsem_ (EQM (to  x3) (i 2)) qd21 O) ) ).


Definition qd11_s := (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x1) (i 2))) qa12 (if_then_elsem_ ((EQM (reveal  x3) (i 2) ) & (EQM (to x2) (i 2))) qa12   (if_then_elsem_ (EQM (reveal  x3) (i 1) ) O (if_then_elsem_ (EQM (to  x3) (i 1)) qd21 O)))).

Definition qd02_s := (if_then_elsem_ (EQM (reveal x3) (i 1) ) O  (if_then_elsem_ (EQM (to x3 ) (i 1)) & (EQM (act x3) new) qa12 O)).
Definition qd10_ss := (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ (EQM (reveal x2) (i 2) ) O (if_then_elsem_ (EQM (to x2) (i 1)) qd20_s (if_then_elsem_ (EQM (to x2) (i 2)) qd11_s O)))).

Definition qd01_ss:=  (if_then_elsem_ ((EQM (reveal x2) (i 2) ) & (EQM (to x1) (i 2))) qd02_s (if_then_elsem_ (EQM (reveal x2) (i 1) ) O (if_then_elsem_ (EQM (to x2 ) (i 1)) & (EQM (act x2) new) qd11_s O))).

Definition t45 := msg (if_then_elsem_ (EQM (reveal x1) (i 1) ) O (if_then_elsem_ (EQM (reveal x1) (i 2) ) O (if_then_elsem_ ((EQM (to x1) (i 1)) & (EQM (act x1) new)) qd10_ss (if_then_elsem_ (EQM (to x1) (i 2)) qd01_ss O) ) )).



Definition phi44 :=  phi3 ++ [ t45 ]. 

***)

