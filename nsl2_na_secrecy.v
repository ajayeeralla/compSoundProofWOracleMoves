   Load "tact_nsl2_na".
       
Axiom eqbrmsgmsg: forall (m1 m2 m3: message), (if_then_else_M (EQ_M m1 m2) m1 m3 ) # (if_then_else_M (EQ_M m1 m2) m2 m3).  
 
Theorem pi1_pi2: phi5 ~ phi25.
Proof.
 
unfold phi5, phi25.
simpl.  
 
(*rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:= (pk (N 1))).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:= (pk (N 2))) at 2.
*)
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t12).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t13).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t14).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t15).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t16).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t26).
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t12).
simpl. 
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t13). simpl. 
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t14). simpl. 
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t15). simpl. 
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t16); simpl. 
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t26); simpl. 
apply IFBRANCH_M5 with (ml1 := [msg (pk (N 1)); msg (pk (N 2))]) (ml2:= [msg (pk (N 1)); msg (pk (N 2))]);try reflexivity; simpl. 




 (b:=  (EQ_M (m x1) (pk (N 2)))) (b':=  (EQ_M (m x1) (pk (N 2)))) (x1:= (pk (N 1))) (y1:= (pk (N 1))) (x2:= (pk (N 2))) (y2:= (pk (N 2))) (x3:= t12) (y3:= t12) (x4 := t13) (y4:= t13) (x5:= t14)(y5:= t14) (x6:= t15) (y6:= t15) (x7:= t16) (y7:=t16)  (x1':= (pk (N 1))) (y1':= (pk (N 1))) (x2':= (pk (N 2))) (y2':= (pk (N 2))) (x3':= t12) (y3':= t12) (x4' := t13) (y4':= t13) (x5':= t14)(y5':= t14) (x6':= t15) (y6':= t15) (x7':= t26) (y7':=t26).

unfold t16, t26.
repeat unf.



apply IFBRANCH_M5 with (ml1:= [msg (pk (N 1)); msg (pk (N 2))])(ml2:= [msg (pk (N 1)); msg (pk (N 2))]); try reflexivity; simpl.

apply IFBRANCH_M4 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (N 3, pk (N 1)) (m x1) (sr 1))] ) (ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (N 3, pk (N 1)) (m x1) (sr 1))]); try reflexivity; simpl.
apply IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (N 3, pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (m x1) (sr 3))]) (ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (N 3, pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (m x1) (sr 3))]); try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:=[msg (pk (N 1)); msg (pk (N 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (N 3, pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (m x1) (sr 3));
    bol (EQ_M (to x3) (i 2));
    msg
      (enc (pi1 (dec x3 (sk (N 2))), (N 4, pk (N 2)))
         (pi2 (dec x3 (sk (N 2)))) (sr 6))])(ml2:=[msg (pk (N 1)); msg (pk (N 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (N 3, pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (m x1) (sr 3));
    bol (EQ_M (to x3) (i 2));
    msg
      (enc (pi1 (dec x3 (sk (N 2))), (N 4, pk (N 2)))
         (pi2 (dec x3 (sk (N 2)))) (sr 6))]); try reflexivity; simpl.
apply IFBRANCH_M1 with (ml1:= ([msg (pk (N 1)); msg (pk (N 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (N 3, pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (m x1) (sr 3));
    bol (EQ_M (to x3) (i 2));
    msg
      (enc (pi1 (dec x3 (sk (N 2))), (N 4, pk (N 2)))
         (pi2 (dec x3 (sk (N 2)))) (sr 6));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4)); 
    msg acc]))(ml2:= ([msg (pk (N 1)); msg (pk (N 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc (N 3, pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (m x1) (sr 3));
    bol (EQ_M (to x3) (i 2));
    msg
      (enc (pi1 (dec x3 (sk (N 2))), (N 4, pk (N 2)))
         (pi2 (dec x3 (sk (N 2)))) (sr 6));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4)); 
    msg acc])); try reflexivity; simpl. 



unfold x3.  simpl.  
unfold sr.  simpl. (*
(***************************rewrite the term that has decryption with (sk (N 2))******************************)
(*************************************************************************************************************)

assert( (f mphi2) # (if_then_else_M (EQ_M (f (mphi2)) (enc ((N 3), pk (N 1)) (pk (N 2)) (sr 1))) (f mphi2) (f mphi2))).
redg. reflexivity. 
(************************************************************************************************************)

assert( (pi1 (dec (f mphi2) (sk (N 2)))) # (if_then_else_M (EQ_M (f (mphi2)) (enc ((N 3), pk (N 1)) (pk (N 2)) (sr 1)))  (pi1 (dec (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)) (sk (N 2))))  (pi1 (dec (f mphi2) (sk (N 2)))))).
rewrite H at 1.

assert( (if_then_else_M
            (EQ_M (f mphi2) (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)))
            (f mphi2) (f mphi2)) # (if_then_else_M
            (EQ_M (f mphi2) (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)))
         (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1))  (f mphi2))).
rewrite eqbrmsgmsg. reflexivity. 
rewrite H0. 

(*************************************************************************************************************)
assert(ifmor:  (pi1
      (dec
         (if_then_else_M
            (EQ_M (f mphi2) (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)))
            (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)) 
            (f mphi2)) (sk (N 2)))) #   (if_then_else_M
            (EQ_M (f mphi2) (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)))   (pi1 (dec (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)) (sk (N 2))))  (pi1 (dec (f mphi2) (sk (N 2)))))).
  
rewrite <- IFSAME_M with (b:= (EQ_M (f mphi2) (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)))). 


Axiom IFEVAL_M1: forall (b:Bool) (m1 m2: message), (if_then_else_M b m1 m2) # (if_then_else_M b (subbol_msg' b TRue m1) (subbol_msg' b FAlse m2)). 
rewrite IFEVAL_M1 . simpl.   redg.
reflexivity. rewrite ifmor.  reflexivity. 
 (*
rewrite dep_enc with (n:=2).
(*
rewrite proj1 .  reflexivity. 
*)*)
 rewrite H0. 




(****************************replace n3 with n15*************************************************************)
(************************************************************************************************************)

assert((L (  (N 3) , (pk (N 1)))) # (L ( (N 15), (pk (N 1))))).
 

apply len_regular. 
split.
assert(lnc # (L (N 3))).
rewrite <- ln with (n:=3). reflexivity. 
assert(lnc # (L (N 15))).
rewrite <- ln with (n:=15). reflexivity.
rewrite <- H1, H2. 
reflexivity. reflexivity. 
(***************************************************************************)
assert((EQ_M  (L (N 3, pk (N 1)))  (L (N 15, pk (N 1))))  ## TRue).
apply EQmsg in H1.
assumption. 
(*************************************************************************)

assert(  (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)) # (if_then_else_M (EQ_M (L (N 3, pk (N 1))) (L (N 15, pk (N 1)))) (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)) O)).
rewrite H2. 
redg.  reflexivity. 
(***************************************************************************)

assert(  (enc (N 15, pk (N 1)) (pk (N 2)) (sr 1)) # (if_then_else_M (EQ_M (L (N 3, pk (N 1))) (L (N 15, pk (N 1)))) (enc (N 15, pk (N 1)) (pk (N 2)) (sr 1)) O)).

rewrite H2.
redg. reflexivity. 
unfold sr in H3, H4. simpl in H3, H4.
unfold sr. simpl.

 x1:= 
(***************************************************************************)
assert(cca2: ( submsg_mylist 1   (if_then_else_M (EQ_M (L (N 3, pk (N 1))) (L (N 15, pk (N 1))))
            (enc (N 3, pk (N 1)) (pk (N 2)) (rs (N 5))) O)
[msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (Mvar 1);
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (pk (N 2)) (rs (N 7)));
    bol
      ((EQ_M (to (f mphi2)) (i 2)) &
       (EQ_M
          (L
             (if_then_else_M
                (EQ_M (f mphi2) (Mvar 1))
               (pi1 (dec (Mvar 1) (sk (N 2)))) (pi1 (dec (f mphi2) (sk (N 2)))))) lnc)) &
      (EQ_M (pi2 (dec (f mphi2) (sk (N 2)))) (pk (N 1)));
    msg
      (enc
         (if_then_else_M
            (EQ_M (f mphi2) (Mvar 1))
            (pi1 (dec (Mvar 1) (sk (N 2)))) (pi1 (dec (f mphi2) (sk (N 2)))), 
         (N 4, pk (N 2))) (pk (N 1)) (rs (N 10)));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4)); 
    msg acc; bol (EQ_M (reveal x4) (i 1)); msg (N 3)]) ~  
(submsg_mylist 1  (if_then_else_M (EQ_M (L (N 3, pk (N 1))) (L (N 15, pk (N 1))))
            (enc (N 15, pk (N 1)) (pk (N 2)) (rs (N 5))) O) [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (Mvar 1);
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (pk (N 2)) (rs (N 7)));
    bol
      ((EQ_M (to (f mphi2)) (i 2)) &
       (EQ_M
          (L
             (if_then_else_M
                (EQ_M (f mphi2) (Mvar 1))
               (pi1 (dec (Mvar 1) (sk (N 2)))) (pi1 (dec (f mphi2) (sk (N 2)))))) lnc)) &
      (EQ_M (pi2 (dec (f mphi2) (sk (N 2)))) (pk (N 1)));
    msg
      (enc
         (if_then_else_M
            (EQ_M (f mphi2) (Mvar 1))
            (pi1 (dec (Mvar 1) (sk (N 2)))) (pi1 (dec (f mphi2) (sk (N 2)))), 
         (N 4, pk (N 2))) (pk (N 1)) (rs (N 10)));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4)); 
    msg acc; bol (EQ_M (reveal x4) (i 1)); msg (N 3)])).
apply ENCCCA2 with (n:=1) (t''' :=  (pi1 (dec (f mphi2) (sk (N 2))))) (t'':= (pi1 (dec (Mvar 1) (sk (N 2)))) ) (t:=  x3 ) (u:= (N 3, pk (N 1))) (u':= (N 15, pk (N 1))) (u'':= O) (n1:= 2) (n2:= 5 ) (n3:= 5)  (l:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (Mvar 1);
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (pk (N 2)) (rs (N 7)));
    bol
      ((EQ_M (to (f mphi2)) (i 2)) &
       (EQ_M
          (L
             (if_then_else_M
                (EQ_M (f mphi2) (Mvar 1))
               (pi1 (dec (Mvar 1) (sk (N 2)))) (pi1 (dec (f mphi2) (sk (N 2)))))) lnc)) &
      (EQ_M (pi2 (dec (f mphi2) (sk (N 2)))) (pk (N 1)));
    msg
      (enc
         (if_then_else_M
            (EQ_M (f mphi2) (Mvar 1))
            (pi1 (dec (Mvar 1) (sk (N 2)))) (pi1 (dec (f mphi2) (sk (N 2)))), 
         (N 4, pk (N 2))) (pk (N 1)) (rs (N 10)));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4)); 
    msg acc; bol (EQ_M (reveal x4) (i 1)); msg (N 3)] ).
split.  reflexivity.
split . reflexivity. 
split .  split. reflexivity. 
split .   split.   
unfold rn_occ_mylist.  simpl. 
reflexivity.
unfold rn_occ_mylist. simpl.  reflexivity.

rewrite <- H3 in cca2.  
rewrite <- H4 in cca2.

simpl in cca2. 

assert(cca21:  [msg (pk (N 1)); msg (pk (N 2));
            bol
              ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) &
              (EQ_M (m x1) (pk (N 2))); msg  (enc (N 3, pk (N 1)) (pk (N 2)) (rs (N 5)));
            bol
              ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
            msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (pk (N 2)) (rs (N 7)));
            bol
              ((EQ_M (to (f mphi2)) (i 2)) &
               (EQ_M
                  (L
                     (if_then_else_M (EQ_M (f mphi2)  (enc (N 3, pk (N 1)) (pk (N 2)) (rs (N 5))))    (pi1 (dec  (enc (N 3, pk (N 1)) (pk (N 2)) (rs (N 5))) (sk (N 2))))
                         (pi1 (dec (f mphi2) (sk (N 2)))))) lnc)) &
              (EQ_M (pi2 (dec (f mphi2) (sk (N 2)))) (pk (N 1)));
            msg
              (enc
                 (if_then_else_M (EQ_M (f mphi2)  (enc (N 3, pk (N 1)) (pk (N 2)) (rs (N 5)))) 
                    (pi1 (dec  (enc (N 3, pk (N 1)) (pk (N 2)) (rs (N 5))) (sk (N 2)))) (pi1 (dec (f mphi2) (sk (N 2)))), 
                 (N 4, pk (N 2))) (pk (N 1)) (rs (N 10)));
            bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4));
            msg acc; bol (EQ_M (reveal x4) (i 1)); 
            msg (N 3)] ~
  [msg (pk (N 1)); msg (pk (N 2));
            bol
              ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) &
              (EQ_M (m x1) (pk (N 2))); msg  (enc (N 15, pk (N 1)) (pk (N 2)) (rs (N 5)));
            bol
              ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
            msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (pk (N 2)) (rs (N 7)));
            bol
              ((EQ_M (to (f mphi2)) (i 2)) &
               (EQ_M
                  (L
                     (if_then_else_M (EQ_M (f mphi2)  (enc (N 15, pk (N 1)) (pk (N 2)) (rs (N 5)))) 
                          (pi1 (dec  (enc (N 15, pk (N 1)) (pk (N 2)) (rs (N 5))) (sk (N 2)))) (pi1 (dec (f mphi2) (sk (N 2)))))) lnc)) &
              (EQ_M (pi2 (dec (f mphi2) (sk (N 2)))) (pk (N 1)));
            msg
              (enc
                 (if_then_else_M (EQ_M (f mphi2)  (enc (N 15, pk (N 1)) (pk (N 2)) (rs (N 5)))) 
                     (pi1 (dec  (enc (N 15, pk (N 1)) (pk (N 2)) (rs (N 5))) (sk (N 2)))) (pi1 (dec (f mphi2) (sk (N 2)))), 
                 (N 4, pk (N 2))) (pk (N 1)) (rs (N 10)));
            bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4));
            msg acc; bol (EQ_M (reveal x4) (i 1)); 
            msg (N 3)]
).
assumption. 
clear cca2.
rewrite <- H0 in cca21. 




rewrite <- H4 in cca21. 

pose proof( IFEVAL_M1).

apply Forall_ELM_EVAL_M1 with (n:=1) (x:= x3)  in H4. simpl in H4.
apply Forall_ELM_EVAL_M1 with (n:=2) (x:= (enc (N 3, pk (N 1)) (pk (N 2)) (sr 5)) )  in H4. simpl in H4.
fold x1 in H4.
(***************************************************************************************************) *)
Focus 2. 
apply IFBRANCH_M4 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))] )
(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))]); try reflexivity; simpl.
apply IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4))]); try reflexivity; simpl. 
apply IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (pk (N 2)) (sr 7))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (pk (N 2)) (sr 7))]); try reflexivity; simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (pk (N 2)) (sr 7));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4)); 
    msg acc])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (pk (N 2)) (sr 7));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4)); 
    msg acc]); try reflexivity; simpl.

Focus 2. 

apply IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))]); try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4)); 
    msg acc])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4)); 
    msg acc]); try reflexivity; simpl. 
apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4)); 
    msg acc;
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (pk (N 1)) (sr 9))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol
      ((EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x2 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4)); 
    msg acc;
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (pk (N 1)) (sr 9))]); try reflexivity; simpl. 
Unfocus. Unfocus. 
Focus 4. 
apply IFBRANCH_M5 with (ml1:= ([msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)))]))(ml2:= ([msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)))])); try reflexivity; simpl.

apply IFBRANCH_M4 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol
      ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol
      ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2))]); try reflexivity; simpl.
apply IFBRANCH_M4 with (ml1:= ([msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol
      ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)))]))(ml2:=  [msg (pk (N 1)); msg (pk (N 2));
   bol
     ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
   bol
     ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
     (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
   msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2));
   bol
     ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)))]); try reflexivity; simpl.
apply IFBRANCH_M3 with (ml1:= ([msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol
      ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4)); 
    msg acc]))(ml2:= ([msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol
      ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4)); 
    msg acc])); try reflexivity; simpl. 
apply IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol
      ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4)); 
    msg acc;
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 8))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol
      ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4)); 
    msg acc;
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 8))]); try reflexivity; simpl. 

apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol
      ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4)); 
    msg acc;
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 8));
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (pk (N 1)) (sr 9))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol
      ((EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc)) &
      (EQ_M (pi2 (dec x1 (sk (N 2)))) (pk (N 1)));
    msg (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) (pk (N 1)) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4)); 
    msg acc;
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc (N 3, pk (N 1)) (pk (N 2)) (sr 8));
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (pk (N 1)) (sr 9))]); try reflexivity; simpl. 
Unfocus. 
