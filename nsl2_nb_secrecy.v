Load "tact_nsl2_nb".  
           
Theorem eqbrmsgmsg: forall (b:Bool) (m m1 m2 m3 m4: message), (if_then_else_M b&(EQ_M m1 m2) (submsg_msg' m m1 m3) m4) #  (if_then_else_M b&(EQ_M m1 m2) (submsg_msg' m m2 m3) m4).
Proof. intros b m m1 m2 m3 m4.
pose proof(EQ_BRmsg_msg' b m m1 m2 m3 m4). 
  
rewrite andB_comm with (b2:= b) in H. assumption. Qed.

Theorem pi1_pi2: phi5 ~ phi25.
Proof.

unfold phi5, phi25.
simpl.  
(**********************IFSAME************************************)
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t12).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t13).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t14).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t15).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t16).
rewrite <-IFSAME_M with (b:= (EQ_M (m x1) (pk (N 2)))) (x:=  t26).
(****************************************************************)
Ltac aply_eqbrmsg  m5 m6  :=
  match goal with
|[|- context[ (if_then_else_M (EQ_M m5 m6) ?M3 ?M4)] ] => rewrite EQ_BRmsg_msg''' with (m1:= m5) (m2:= m6) (m:= m5) (m3:= M3) (m4:= M4) 
end. 

 Definition xt :=  [pk (N 1); pk (N 2);
          if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
            (enc (N 3, pk (N 1)) (Mvar 0) (sr 1))
            (if_then_else_M (EQ_M (to x1) (i 2))
               (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) 
                  (pk (N 1)) (sr 2)) O)].

Definition x2' :=  (f  xt).
Definition x3' := (f
         [pk (N 1); pk (N 2);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (enc (N 3, pk (N 1)) (Mvar 0) (sr 1))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) 
                 (pk (N 1)) (sr 2)) O);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
              (enc (pi1 (pi2 (dec x2' (sk (N 1))))) (Mvar 0) (sr 3))
              (if_then_else_M (EQ_M (to x2') (i 2))
                 (enc (pi1 (dec x2' (sk (N 2))), (N 4, pk (N 2))) 
                    (pk (N 1)) (sr 4)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
                 (enc (N 3, pk (N 1)) (m x2') (sr 5))
                 (if_then_else_M
                    (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4))
                    acc O)) O)]).
Definition x4' :=  (f
         [pk (N 1); pk (N 2);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (enc (N 3, pk (N 1)) (Mvar 0) (sr 1))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) 
                 (pk (N 1)) (sr 2)) O);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
              (enc (pi1 (pi2 (dec x2' (sk (N 1))))) (Mvar 0) (sr 3))
              (if_then_else_M (EQ_M (to x2') (i 2))
                 (enc (pi1 (dec x2' (sk (N 2))), (N 4, pk (N 2))) 
                    (pk (N 1)) (sr 4)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
                 (enc (N 3, pk (N 1)) (m x2') (sr 5))
                 (if_then_else_M
                    (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4))
                    acc O)) O);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
              (if_then_else_M (EQ_M (to x3') (i 2))
                 (enc (pi1 (dec x3' (sk (N 2))), (N 4, pk (N 2))) 
                    (pk (N 1)) (sr 6)) O)
              (if_then_else_M (EQ_M (to x2') (i 2))
                 (if_then_else_M
                    ((EQ_M (to x3') (i 1)) &
                     (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                    (enc (pi1 (pi2 (dec x3' (sk (N 1))))) (Mvar 0) (sr 7))
                    (if_then_else_M
                       (EQ_M (to x3') (i 2)) &
                       (EQ_M (dec x3' (sk (N 2))) (N 4)) acc O)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
                 (if_then_else_M
                    ((EQ_M (to x3') (i 1)) &
                     (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                    (enc (pi1 (pi2 (dec x3' (sk (N 1))))) (Mvar 0) (sr 7))
                    (if_then_else_M
                       (EQ_M (to x3') (i 2)) &
                       (EQ_M (dec x3' (sk (N 2))) (N 4)) acc O))
                 (if_then_else_M
                    (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4))
                    (if_then_else_M
                       (EQ_M (to x3') (i 1)) & (EQ_M (act x3') new)
                       (enc (N 3, pk (N 1)) (Mvar 0) (sr 8)) O) O)) O)]).
Definition x5' :=  (f
         [pk (N 1); pk (N 2); t12; t13;
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
              (if_then_else_M (EQ_M (to x3') (i 2))
                 (enc (pi1 (dec x3' (sk (N 2))), (N 4, pk (N 2))) 
                    (pk (N 1)) (sr 6)) O)
              (if_then_else_M (EQ_M (to x2') (i 2))
                 (if_then_else_M
                    ((EQ_M (to x3') (i 1)) &
                     (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                    (enc (pi1 (pi2 (dec x3' (sk (N 1))))) (Mvar 0) (sr 7))
                    (if_then_else_M
                       (EQ_M (to x3') (i 2)) &
                       (EQ_M (dec x3' (sk (N 2))) (N 4)) acc O)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
                 (if_then_else_M
                    ((EQ_M (to x3') (i 1)) &
                     (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                    (enc (pi1 (pi2 (dec x3' (sk (N 1))))) (Mvar 0) (sr 7))
                    (if_then_else_M
                       (EQ_M (to x3') (i 2)) &
                       (EQ_M (dec x3' (sk (N 2))) (N 4)) acc O))
                 (if_then_else_M
                    (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4))
                    (if_then_else_M
                       (EQ_M (to x3') (i 1)) & (EQ_M (act x3') new)
                       (enc (N 3, pk (N 1)) (Mvar 0) (sr 8)) O) O)) O);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
              (if_then_else_M (EQ_M (to x3') (i 2))
                 (if_then_else_M
                    (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4))
                    acc O) O)
              (if_then_else_M (EQ_M (to x2') (i 2))
                 (if_then_else_M
                    ((EQ_M (to x3') (i 1)) &
                     (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                    (if_then_else_M
                       (EQ_M (to x4') (i 2)) &
                       (EQ_M (dec x4' (sk (N 2))) (N 4)) acc O)
                    (if_then_else_M
                       (EQ_M (to x3') (i 2)) &
                       (EQ_M (dec x3' (sk (N 2))) (N 4))
                       (if_then_else_M
                          ((EQ_M (to x4') (i 1)) &
                           (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                          (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                          (enc (pi1 (pi2 (dec x4' (sk (N 1))))) (Mvar 0) (sr 9))
                          O) O)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
                 (if_then_else_M
                    ((EQ_M (to x3') (i 1)) &
                     (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                    (if_then_else_M
                       (EQ_M (to x4') (i 2)) &
                       (EQ_M (dec x4' (sk (N 2))) (N 4)) acc O)
                    (if_then_else_M
                       (EQ_M (to x3') (i 2)) &
                       (EQ_M (dec x3' (sk (N 2))) (N 4))
                       (if_then_else_M
                          ((EQ_M (to x4') (i 1)) &
                           (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                          (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                          (enc (pi1 (pi2 (dec x4' (sk (N 1))))) (Mvar 0) (sr 9))
                          O) O))
                 (if_then_else_M
                    (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4))
                    (if_then_else_M
                       (EQ_M (to x3') (i 1)) & (EQ_M (act x3') new)
                       (if_then_else_M
                          ((EQ_M (to x4') (i 1)) &
                           (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                          (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                          (enc (pi1 (pi2 (dec x4' (sk (N 1))))) (Mvar 0) (sr 9))
                          O) O) O)) O)]).

Definition t12' := (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
          (enc (N 3, pk (N 1)) (Mvar 0) (sr 1))
          (if_then_else_M (EQ_M (to x1) (i 2))
             (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) 
                (pk (N 1)) (sr 2)) O)).
Definition t13' :=    (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
            (enc (pi1 (pi2 (dec x2' (sk (N 1))))) (Mvar 0) (sr 3))
            (if_then_else_M (EQ_M (to x2') (i 2))
               (enc (pi1 (dec x2' (sk (N 2))), (N 4, pk (N 2))) 
                  (pk (N 1)) (sr 4)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
               (enc (N 3, pk (N 1)) (m x2') (sr 5))
               (if_then_else_M
                  (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4)) acc
                  O)) O)).
Definition t14' :=(if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
            (if_then_else_M (EQ_M (to x3') (i 2))
               (enc (pi1 (dec x3' (sk (N 2))), (N 4, pk (N 2))) 
                  (pk (N 1)) (sr 6)) O)
            (if_then_else_M (EQ_M (to x2') (i 2))
               (if_then_else_M
                  ((EQ_M (to x3') (i 1)) &
                   (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                  (enc (pi1 (pi2 (dec x3' (sk (N 1))))) (Mvar 0) (sr 7))
                  (if_then_else_M
                     (EQ_M (to x3') (i 2)) & (EQ_M (dec x3' (sk (N 2))) (N 4))
                     acc O)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
               (if_then_else_M
                  ((EQ_M (to x3') (i 1)) &
                   (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                  (enc (pi1 (pi2 (dec x3' (sk (N 1))))) (Mvar 0) (sr 7))
                  (if_then_else_M
                     (EQ_M (to x3') (i 2)) & (EQ_M (dec x3' (sk (N 2))) (N 4))
                     acc O))
               (if_then_else_M
                  (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4))
                  (if_then_else_M (EQ_M (to x3') (i 1)) & (EQ_M (act x3') new)
                     (enc (N 3, pk (N 1)) (Mvar 0) (sr 8)) O) O)) O)).
Definition t15' := (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
            (if_then_else_M (EQ_M (to x3') (i 2))
               (if_then_else_M
                  (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4)) acc
                  O) O)
            (if_then_else_M (EQ_M (to x2') (i 2))
               (if_then_else_M
                  ((EQ_M (to x3') (i 1)) &
                   (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                  (if_then_else_M
                     (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4))
                     acc O)
                  (if_then_else_M
                     (EQ_M (to x3') (i 2)) & (EQ_M (dec x3' (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4') (i 1)) &
                         (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                        (enc (pi1 (pi2 (dec x4' (sk (N 1))))) (Mvar 0) (sr 9)) O)
                     O)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
               (if_then_else_M
                  ((EQ_M (to x3') (i 1)) &
                   (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                  (if_then_else_M
                     (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4))
                     acc O)
                  (if_then_else_M
                     (EQ_M (to x3') (i 2)) & (EQ_M (dec x3' (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4') (i 1)) &
                         (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                        (enc (pi1 (pi2 (dec x4' (sk (N 1))))) (Mvar 0) (sr 9)) O)
                     O))
               (if_then_else_M
                  (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4))
                  (if_then_else_M (EQ_M (to x3') (i 1)) & (EQ_M (act x3') new)
                     (if_then_else_M
                        ((EQ_M (to x4') (i 1)) &
                         (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                        (enc (pi1 (pi2 (dec x4' (sk (N 1))))) (Mvar 0) (sr 9)) O)
                     O) O)) O)).
Definition t16' :=  (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
            (if_then_else_M (EQ_M (to x3') (i 2))
               (if_then_else_M
                  (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4))
                  (if_then_else_M
                     (EQ_M (reveal x5') (i 1)) & (EQ_M (m x1) (pk (N 2)))
                     (N 3)
                     (if_then_else_M
                        (EQ_M (reveal x5') (i 2)) & (EQ_M (m x1) (pk (N 2)))
                        (N 4) O)) O) O)
            (if_then_else_M (EQ_M (to x2') (i 2))
               (if_then_else_M
                  ((EQ_M (to x3') (i 1)) &
                   (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                  (if_then_else_M
                     (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4))
                     (if_then_else_M
                        (EQ_M (reveal x5') (i 1)) & (EQ_M (m x1) (pk (N 2)))
                        (N 3)
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 2)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 4) O)) O)
                  (if_then_else_M
                     (EQ_M (to x3') (i 2)) & (EQ_M (dec x3' (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4') (i 1)) &
                         (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 3)
                           (if_then_else_M
                              (EQ_M (reveal x5') (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 4) O)) O) O)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
               (if_then_else_M
                  ((EQ_M (to x3') (i 1)) &
                   (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                  (if_then_else_M
                     (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4))
                     (if_then_else_M
                        (EQ_M (reveal x5') (i 1)) & (EQ_M (m x1) (pk (N 2)))
                        (N 3)
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 2)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 4) O)) O)
                  (if_then_else_M
                     (EQ_M (to x3') (i 2)) & (EQ_M (dec x3' (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4') (i 1)) &
                         (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 3)
                           (if_then_else_M
                              (EQ_M (reveal x5') (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 4) O)) O) O))
               (if_then_else_M
                  (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4))
                  (if_then_else_M (EQ_M (to x3') (i 1)) & (EQ_M (act x3') new)
                     (if_then_else_M
                        ((EQ_M (to x4') (i 1)) &
                         (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 3)
                           (if_then_else_M
                              (EQ_M (reveal x5') (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 4) O)) O) O) O)) O)).
Definition t26' :=  (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2') (i 1)) & (EQ_M (pi1 (dec x2' (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2' (sk (N 1))))) (Mvar 0))
            (if_then_else_M (EQ_M (to x3') (i 2))
               (if_then_else_M
                  (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4))
                  (if_then_else_M
                     (EQ_M (reveal x5') (i 1)) & (EQ_M (m x1) (pk (N 2)))
                     (N 14)
                     (if_then_else_M
                        (EQ_M (reveal x5') (i 2)) & (EQ_M (m x1) (pk (N 2)))
                        (N 14)
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 3)
                           (if_then_else_M
                              (EQ_M (reveal x5') (i 1)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 4) O)))) O) O)
            (if_then_else_M (EQ_M (to x2') (i 2))
               (if_then_else_M
                  ((EQ_M (to x3') (i 1)) &
                   (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                  (if_then_else_M
                     (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4))
                     (if_then_else_M
                        (EQ_M (reveal x5') (i 1)) & (EQ_M (m x1) (pk (N 2)))
                        (N 14)
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 2)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5') (i 1)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 3)
                              (if_then_else_M
                                 (EQ_M (reveal x5') (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 4) O)))) O)
                  (if_then_else_M
                     (EQ_M (to x3') (i 2)) & (EQ_M (dec x3' (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4') (i 1)) &
                         (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5') (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 14)
                              (if_then_else_M
                                 (EQ_M (reveal x5') (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 3)
                                 (if_then_else_M
                                    (EQ_M (reveal x5') (i 1)) &
                                    (EQ_M (m x1) (pk (N 2))) 
                                    (N 4) O)))) O) O)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2') (i 1)) & (EQ_M (act x2') new)
               (if_then_else_M
                  ((EQ_M (to x3') (i 1)) &
                   (EQ_M (pi1 (dec x3' (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3' (sk (N 1))))) (Mvar 0))
                  (if_then_else_M
                     (EQ_M (to x4') (i 2)) & (EQ_M (dec x4' (sk (N 2))) (N 4))
                     (if_then_else_M
                        (EQ_M (reveal x5') (i 1)) & (EQ_M (m x1) (pk (N 2)))
                        (N 14)
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 2)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5') (i 1)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 3)
                              (if_then_else_M
                                 (EQ_M (reveal x5') (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 4) O)))) O)
                  (if_then_else_M
                     (EQ_M (to x3') (i 2)) & (EQ_M (dec x3' (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4') (i 1)) &
                         (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5') (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 14)
                              (if_then_else_M
                                 (EQ_M (reveal x5') (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 3)
                                 (if_then_else_M
                                    (EQ_M (reveal x5') (i 1)) &
                                    (EQ_M (m x1) (pk (N 2))) 
                                    (N 4) O)))) O) O))
               (if_then_else_M
                  (EQ_M (to x2') (i 2)) & (EQ_M (dec x2' (sk (N 2))) (N 4))
                  (if_then_else_M (EQ_M (to x3') (i 1)) & (EQ_M (act x3') new)
                     (if_then_else_M
                        ((EQ_M (to x4') (i 1)) &
                         (EQ_M (pi1 (dec x4' (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4' (sk (N 1))))) (Mvar 0))
                        (if_then_else_M
                           (EQ_M (reveal x5') (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5') (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 14)
                              (if_then_else_M
                                 (EQ_M (reveal x5') (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 3)
                                 (if_then_else_M
                                    (EQ_M (reveal x5') (i 1)) &
                                    (EQ_M (m x1) (pk (N 2))) 
                                    (N 4) O)))) O) O) O)) O)).

 Ltac aply_eqbrmsg1 m5 m6 m7 m8 := 
  match goal with
|[|- context[ (if_then_else_M (EQ_M m5 m6) m7 ?M4)] ] => pose proof(EQ_BRmsg_msg m8 M4 0 1 0); simpl ;
 match goal with
|[H: context[ (EQ_M (Mvar 0) (Mvar 1)) ] |- _ ] =>  apply Forall_ELM_EVAL_M1 with (x:= m5) (n:= 0) in H;  apply Forall_ELM_EVAL_M1 with (x:= m6) (n:= 1) in H; simpl in H; rewrite H; clear H  end end.

aply_eqbrmsg1 (m x1) (pk (N 2)) t12 t12'.
aply_eqbrmsg1 (m x1) (pk (N 2)) t13 t13'.
aply_eqbrmsg1 (m x1) (pk (N 2)) t14 t14'.
aply_eqbrmsg1 (m x1) (pk (N 2)) t15 t15'.
aply_eqbrmsg1 (m x1) (pk (N 2)) t16 t16'.
aply_eqbrmsg1 (m x1) (pk (N 2)) t26 t26'.



apply Forall_ELM_EVAL_M1 with (x:= (m x1)) (n:= 0) in H.
apply Forall_ELM_EVAL_M1 with (x:= (pk (N 2))) (n:= 1) in H.
simpl in H.  fold x1 in H.
assert(H1: (if_then_else_M
            (if_then_else_B
               (EQ_M (to (f [pi1 (k (N 1)); pi1 (k (N 2))])) (i 1))
               (EQ_M (act (f [pi1 (k (N 1)); pi1 (k (N 2))])) new) FAlse)
            (enc (N 3, pi1 (k (N 1))) (m (f [pi1 (k (N 1)); pi1 (k (N 2))]))
               (rs (N 5)))
            (if_then_else_M
               (EQ_M (to (f [pi1 (k (N 1)); pi1 (k (N 2))])) (i 2))
               (enc
                  (pi1
                     (dec (f [pi1 (k (N 1)); pi1 (k (N 2))]) (pi2 (k (N 2)))),
                  (N 4, pi1 (k (N 2)))) (pi1 (k (N 1))) 
                  (rs (N 6))) O)) # t12). unf_trm.  repeat unf.
rewrite <- H. 

aply_eqbrmsg1 (m x1) (pk (N 2)) t12 t12'.

(*
aply_eqbrmsg1  (m x1) (pk (N 2)) t12. 
aply_eqbrmsg1 (m x1) (pk (N 2)) t13.
aply_eqbrmsg1 (m x1) (pk (N 2)) t14.
aply_eqbrmsg1 (m x1) (pk (N 2)) t15.
aply_eqbrmsg1 (m x1) (pk (N 2)) t16.
aply_eqbrmsg1 (m x1) (pk (N 2)) t26.
*)




rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t12);simpl. 

rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t13); simpl. 
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t14); simpl. 
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t15); simpl. 
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t16); simpl. 
rewrite EQ_BRmsg_msg''' with (m1:= (m x1) )(m2:= (pk (N 2))) (m:= (m x1)) (m3:= t26); simpl. 


(*********************************************************************************)
Ltac aply_eqbrmsg2 m5 m6:= 
match goal with 
|[|- context[ (if_then_else_M (if_then_else_B ?B (EQ_M  m5 m6) FAlse) ?M3 ?M4) ] ] => rewrite  eqbrmsgmsg with (b:= B) (m:= m5) (m1:= m5) (m2:= m6) (m3:= M3) (m4:= M4)
end. 
 repeat aply_eqbrmsg2 (pi2 (dec (f mphi0) (pi2 (k (N 2))))) (pi1 (k (N 1))). simpl. 
 repeat aply_eqbrmsg2 (pi2 (dec (f mphi1) (pi2 (k (N 2))))) (pi1 (k (N 1))). simpl. 
repeat aply_eqbrmsg2 (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (pi1 (k (N 1))). simpl. 
(*******************************************************************************)
rewrite IFEVAL_M'  with (t2:= t26).  simpl. 
 repeat redg. 
rewrite IFEVAL_M' with (t2:= t16).  simpl. 
 repeat redg. 
(*****************************************************************************)
apply IFBRANCH_M5 with (ml1:= [msg (pk (N 1)); msg (pk (N 2))])(ml2:= [msg (pk (N 1)); msg (pk (N 2))]); try reflexivity; simpl.

apply IFBRANCH_M5 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)))])(ml2:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)))]); try reflexivity; simpl.
apply IFBRANCH_M4 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol
      (if_then_else_B (EQ_M (to (f mphi0)) (i 1)) (EQ_M (act (f mphi0)) new)
         FAlse); msg (enc (N 3, pi1 (k (N 1))) (pk (N 2)) (rs (N 5)))]) (ml2:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol
      (if_then_else_B (EQ_M (to (f mphi0)) (i 1)) (EQ_M (act (f mphi0)) new)
         FAlse); msg (enc (N 3, pi1 (k (N 1))) (pk (N 2)) (rs (N 5)))]); try reflexivity; simpl.

apply IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol
      (if_then_else_B (EQ_M (to (f mphi0)) (i 1)) (EQ_M (act (f mphi0)) new)
         FAlse); msg (enc (N 3, pi1 (k (N 1))) (pk (N 2)) (rs (N 5)));
    bol
      (if_then_else_B
         (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
            (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (N 3)) FAlse)
         (EQ_M (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2))) FAlse);
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2)) (rs (N 7)))])(ml2:=[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol
      (if_then_else_B (EQ_M (to (f mphi0)) (i 1)) (EQ_M (act (f mphi0)) new)
         FAlse); msg (enc (N 3, pi1 (k (N 1))) (pk (N 2)) (rs (N 5)));
    bol
      (if_then_else_B
         (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
            (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (N 3)) FAlse)
         (EQ_M (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2))) FAlse);
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2)) (rs (N 7)))]); try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol
      (if_then_else_B (EQ_M (to (f mphi0)) (i 1)) (EQ_M (act (f mphi0)) new)
         FAlse); msg (enc (N 3, pi1 (k (N 1))) (pk (N 2)) (rs (N 5)));
    bol
      (if_then_else_B
         (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
            (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (N 3)) FAlse)
         (EQ_M (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2))) FAlse);
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2)) (rs (N 7)));
    bol
      (EQ_M (to (f mphi2)) (i 2)) &
      (EQ_M (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (pi1 (k (N 1))));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), (N 4, pi1 (k (N 2))))
         (pi1 (k (N 1))) (rs (N 10)))])(ml2:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol
      (if_then_else_B (EQ_M (to (f mphi0)) (i 1)) (EQ_M (act (f mphi0)) new)
         FAlse); msg (enc (N 3, pi1 (k (N 1))) (pk (N 2)) (rs (N 5)));
    bol
      (if_then_else_B
         (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
            (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (N 3)) FAlse)
         (EQ_M (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2))) FAlse);
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2)) (rs (N 7)));
    bol
      (EQ_M (to (f mphi2)) (i 2)) &
      (EQ_M (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (pi1 (k (N 1))));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), (N 4, pi1 (k (N 2))))
         (pi1 (k (N 1))) (rs (N 10)))]); try reflexivity; simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol
      (if_then_else_B (EQ_M (to (f mphi0)) (i 1)) (EQ_M (act (f mphi0)) new)
         FAlse); msg (enc (N 3, pi1 (k (N 1))) (pk (N 2)) (rs (N 5)));
    bol
      (if_then_else_B
         (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
            (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (N 3)) FAlse)
         (EQ_M (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2))) FAlse);
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2)) (rs (N 7)));
    bol
      (EQ_M (to (f mphi2)) (i 2)) &
      (EQ_M (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (pi1 (k (N 1))));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), (N 4, pi1 (k (N 2))))
         (pi1 (k (N 1))) (rs (N 10)));
    bol
      (if_then_else_B (EQ_M (to (f mphi3)) (i 2))
         (EQ_M (dec (f mphi3) (pi2 (k (N 2)))) (N 4)) FAlse); 
    msg acc]) (ml2:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol
      (if_then_else_B (EQ_M (to (f mphi0)) (i 1)) (EQ_M (act (f mphi0)) new)
         FAlse); msg (enc (N 3, pi1 (k (N 1))) (pk (N 2)) (rs (N 5)));
    bol
      (if_then_else_B
         (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
            (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (N 3)) FAlse)
         (EQ_M (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2))) FAlse);
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) (pk (N 2)) (rs (N 7)));
    bol
      (EQ_M (to (f mphi2)) (i 2)) &
      (EQ_M (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (pi1 (k (N 1))));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), (N 4, pi1 (k (N 2))))
         (pi1 (k (N 1))) (rs (N 10)));
    bol
      (if_then_else_B (EQ_M (to (f mphi3)) (i 2))
         (EQ_M (dec (f mphi3) (pi2 (k (N 2)))) (N 4)) FAlse); 
    msg acc]); try reflexivity; simpl.
fold (sk (N 2)) (sk (N 1)) (pk (N 2)) (pk (N 1)) x1 x2 x3' x4 x5.


(***************************rewrite the term that has decryption with (sk (N 2))******************************)
(*************************************************************************************************************)

assert( (f mphi2) # (if_then_else_M (EQ_M (f (mphi2)) (enc ((N 3), pk (N 1)) (pk (N 2)) (sr 1))) (f mphi2) (f mphi2))).
redg. reflexivity. 
(************************************************************************************************************)
 
assert( (pi1 (dec (f mphi2) (sk (N 2)))) # (if_then_else_M (EQ_M (f (mphi2)) (enc ((N 3), pk (N 1)) (pk (N 2)) (sr 1)))  (N 3)  (pi1 (dec (f mphi2) (sk (N 2)))))).
rewrite H at 1.

assert( (if_then_else_M
            (EQ_M (f mphi2) (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)))
            (f mphi2) (f mphi2)) # (if_then_else_M
            (EQ_M (f mphi2) (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)))
         (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1))  (f mphi2))).
rewrite EQ_BRmsg_msg''' with (m:= x3) (m1:= x3) (m2:= (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1))) (m3:= x3). reflexivity. 

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
reflexivity. rewrite ifmor.
 
rewrite dep_enc with (n:=2).
rewrite proj1 .  reflexivity. 

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

(***************************************************************************)
assert(cca2: ( submsg_mylist 1   (if_then_else_M (EQ_M (L (N 3, pk (N 1))) (L (N 15, pk (N 1))))
             (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)) O) 
[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol (if_then_else_B (EQ_M (to x1) (i 1)) (EQ_M (act x1) new) FAlse);
    msg (Mvar 1);
    bol
      (if_then_else_B
         (if_then_else_B (EQ_M (to x2) (i 1))
            (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3)) FAlse)
         (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (pk (N 2))) FAlse);
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (pk (N 2)) (rs (N 7)));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (pi2 (dec x3 (sk (N 2)))) (pk (N 1)));
    msg
      (enc
         (if_then_else_M
            (EQ_M (f mphi2) (Mvar 1)) 
            (N 3) (pi1 (dec (f mphi2) (sk (N 2)))), 
         (N 4, pk (N 2))) (pk (N 1)) (rs (N 10)));
    bol
      (if_then_else_B (EQ_M (to x4) (i 2)) (EQ_M (dec x4 (sk (N 2))) (N 4))
         FAlse); msg acc;
    bol
      (if_then_else_B (EQ_M (reveal x5) (i 1)) (EQ_M (pk (N 2)) (pk (N 2)))
         FAlse); msg (N 3)]) ~  
(submsg_mylist 1  (if_then_else_M (EQ_M (L (N 3, pk (N 1))) (L (N 15, pk (N 1))))
            (enc (N 15, pk (N 1)) (pk (N 2)) (sr 1)) O)  [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol (if_then_else_B (EQ_M (to x1) (i 1)) (EQ_M (act x1) new) FAlse);
    msg (Mvar 1);
    bol
      (if_then_else_B
         (if_then_else_B (EQ_M (to x2) (i 1))
            (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3)) FAlse)
         (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (pk (N 2))) FAlse);
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (pk (N 2)) (rs (N 7)));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (pi2 (dec x3 (sk (N 2)))) (pk (N 1)));
    msg
      (enc
         (if_then_else_M
            (EQ_M (f mphi2) (Mvar 1)) 
            (N 3) (pi1 (dec (f mphi2) (sk (N 2)))), 
         (N 4, pk (N 2))) (pk (N 1)) (rs (N 10)));
    bol
      (if_then_else_B (EQ_M (to x4) (i 2)) (EQ_M (dec x4 (sk (N 2))) (N 4))
         FAlse); msg acc;
    bol
      (if_then_else_B (EQ_M (reveal x5) (i 1)) (EQ_M (pk (N 2)) (pk (N 2)))
         FAlse); msg (N 3)])).
pose proof(ENCCCA2). 
unfold sr.
unfold sr   in H4, H3.  
apply ENCCCA2 with (n:=1) (t''' := (pi1 (dec (f mphi2) (sk (N 2))))) (t'':= (N 3 )) (t:= (f mphi2)) (u:= (N 3, pk (N 1))) (u':=(N 15, pk (N 1))) (u'':= O) (n1:= 2) (n2:=5) (n3:= 5)  (l:=  [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (m x1) (pk (N 2)));
    bol (if_then_else_B (EQ_M (to x1) (i 1)) (EQ_M (act x1) new) FAlse);
    msg (Mvar 1);
    bol
      (if_then_else_B
         (if_then_else_B (EQ_M (to x2) (i 1))
            (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3)) FAlse)
         (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (pk (N 2))) FAlse);
    msg (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (pk (N 2)) (rs (N 7)));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (pi2 (dec x3 (sk (N 2)))) (pk (N 1)));
    msg
      (enc
         (if_then_else_M
            (EQ_M (f mphi2) (Mvar 1)) 
            (N 3) (pi1 (dec (f mphi2) (sk (N 2)))), 
         (N 4, pk (N 2))) (pk (N 1)) (rs (N 10)));
    bol
      (if_then_else_B (EQ_M (to x4) (i 2)) (EQ_M (dec x4 (sk (N 2))) (N 4))
         FAlse); msg acc;
    bol
      (if_then_else_B (EQ_M (reveal x5) (i 1)) (EQ_M (pk (N 2)) (pk (N 2)))
         FAlse); msg (N 3)]).
split. reflexivity. 
split. reflexivity. 
split .  split.  reflexivity.
reflexivity. 
split.  simpl. 
reflexivity. 
simpl. 
reflexivity.
rewrite <- H3 in cca2.
rewrite <- H4 in cca2.

Eval compute in x2.
Eval compute in x3. 
pose proof( IF).

apply Forall_ELM_EVAL_M1 with (n:=1) (x:= x3)  in H4. simpl in H4.
apply Forall_ELM_EVAL_M1 with (n:=2) (x:= (enc (N 3, pk (N 1)) (pk (N 2)) (sr 1)) )  in H4. simpl in H4.
fold x1 in H4.
assert(  (f [pi1 (k (N 1)); pi1 (k (N 2))]) # x1). 
reflexivity. 
rewrite H5 in H4. 
assert(  (f [pi1 (k (N 1)); pi1 (k (N 2)) ; if_then_else_M
               (if_then_else_B
                  (if_then_else_B (EQ_M (to x1) (i 1)) 
                     (EQ_M (act x1) new) FAlse) (EQ_M (m x1) (pi1 (k (N 2))))
                  FAlse)
               (enc (N 3, pi1 (k (N 1))) (pi1 (k (N 2))) (rs (N 1)))
               (if_then_else_M
                  (if_then_else_B
                     (if_then_else_B (EQ_M (to x1) (i 2))
                        (EQ_M (L (pi1 (dec x1 (pi2 (k (N 2))))))
                           {{1 := x3}}(lnc)) FAlse)
                     (EQ_M (pi2 (dec x1 (pi2 (k (N 2))))) (pi1 (k (N 1))))
                     FAlse)
                  (enc (pi1 (dec x1 (pi2 (k (N 2)))), (N 4, pi1 (k (N 2))))
                     (pi1 (k (N 1))) (rs (N 1))) O)]) # x1). 
reflexivity. 
rewrite H. 

Focus 2. 
apply IFBRANCH_M4 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))]); try reflexivity; simpl.
apply IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4))]); try reflexivity; simpl. 
apply IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 6))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 6))]); try reflexivity; simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 6));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (nc (N 4))); 
    msg acc])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 6));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (nc (N 4))); 
    msg acc]); try reflexivity; simpl.

Focus 2. 

apply IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))]); try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (nc (N 4))); 
    msg acc])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (nc (N 4))); 
    msg acc]); try reflexivity; simpl. 
apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (nc (N 4))); 
    msg acc;
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 10))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 1));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x2 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x2 (sk (N 2)))) (sr 4));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (nc (N 4))); 
    msg acc;
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 10))]); try reflexivity; simpl. 
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
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2))]); try reflexivity; simpl.
apply IFBRANCH_M3 with (ml1:= ([msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5))]))(ml2:= ([msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5))])); try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 6))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 6))]); try reflexivity; simpl. 
apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 6));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (nc (N 4))); 
    msg acc])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 6));
    bol (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (nc (N 4))); 
    msg acc]); try reflexivity; simpl. 
Focus 2. 
apply IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))]); try reflexivity; simpl. 
apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (nc (N 4))); 
    msg acc;
    msg
      (if_then_else_M
         ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
         (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
         (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 10)) O)])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (nc (N 4))); 
    msg acc;
    msg
      (if_then_else_M
         ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
         (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
         (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 10)) O)]); try reflexivity; simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (nc (N 4))); 
    msg acc;
    msg
      (if_then_else_M
         ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
         (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
         (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 10)) O);
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 5));
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1));
    bol (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (nc (N 4))); 
    msg acc;
    msg
      (if_then_else_M
         ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
         (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
         (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 10)) O);
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))]); try reflexivity; simpl.
Unfocus.
Focus 3. 
apply IFBRANCH_M4 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)))]) (ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)))]);try reflexivity; simpl.
apply IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (nc (N 4))); 
    msg acc]) (ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (nc (N 4))); 
    msg acc]); try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (nc (N 4))); 
    msg acc;
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 7))])(ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (nc (N 4))); 
    msg acc;
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 7))]); try reflexivity; simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (nc (N 4))); 
    msg acc;
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 7));
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 10))]) (ml2:= [msg (pk (N 1)); msg (pk (N 2));
    bol
      ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x1) (i 2)) & (EQ_M (L (pi1 (dec x1 (sk (N 2))))) lnc);
    msg
      (enc (pi1 (dec x1 (sk (N 2))), ((nc (N 4)), pk (N 2)))
         (pi2 (dec x1 (sk (N 2)))) (sr 2));
    bol
      ((EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)) & (EQ_M (m x1) (pk (N 2)));
    bol (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (nc (N 4))); 
    msg acc;
    bol
      ((EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)) & (EQ_M (m x1) (pk (N 2)));
    msg (enc ((nc (N 3)), pk (N 1)) (m x1) (sr 7));
    bol
      ((EQ_M (to x4) (i 1)) & (EQ_M (pi1 (dec x4 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1));
    msg (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 10))]); try reflexivity; simpl.
Unfocus.
Unfocus.

simpl.  simpl. 

 (*
apply RESTR_rev with (ml1:= [t15; t14; t13; t12; msg (pk (N 2)); msg (pk (N 1))]) (ml2:=  [t25; t14; t13; t12; msg (pk (N 2)); msg (pk (N 1))]).

(*assert( (ostomsg t25) # O). *)
repeat unf. simpl.
*)
repeat unf; simpl.
Ltac aply_andBcomm m1 :=
match goal with
|[|- context[ ?B & (EQ_M ?M m1) ] ] => rewrite andB_comm with (b1:= B) (b2:= (EQ_M M m1))
end.
repeat aply_andBcomm (nc (N 3)).

pose proof (EQ_BRmsg_msg').
Ltac aply_eqbr B m5  :=
 match goal with
| [|- context [(if_then_else_M ((EQ_M ?M1 m5) & B) ?M3 ?M4)] ] => rewrite EQ_BRmsg_msg'  with (m1:= M1) (m2:= m5) (m:= M1) (b:= B) (m3:= M3) (m4:=M4)    end.

 aply_eqbr  (EQ_M (to x2) (i 1)) (nc (N 3)). 
simpl.
 


 repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc (N 3))) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x2) (i 1))) (m3:=      (if_then_else_M
                           ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
                             (EQ_M (to x1) (i 1))) &
                            (notb (EQ_M (act x2) new))) & 
                           (EQ_M (act x1) new) (pi1 (dec x2 (sk (N 1))))
                           (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                              (if_then_else_M (EQ_M (to x3) (i 2))
                                 (enc
                                    (pi1 (dec x3 (sk (N 2))),
                                    ((nc (N 4)), pk (N 2)))
                                    (pi2 (dec x3 (sk (N 2)))) 
                                    (sr 6)) O)))). 
simpl. 
repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc (N 3))) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x2) (i 1))) (m3:=    (if_then_else_M
                           ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
                             (EQ_M (to x1) (i 1))) &
                            (notb (EQ_M (act x2) new))) & 
                           (EQ_M (act x1) new)
                           (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                              (if_then_else_M (EQ_M (to x4) (i 2))
                                 (enc
                                    (pi1 (dec x4 (sk (N 2))),
                                    ((nc (N 4)), pk (N 2)))
                                    (pi2 (dec x4 (sk (N 2)))) 
                                    (sr 9)) O))
                           (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                              (if_then_else_M (EQ_M (to x3) (i 2))
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x1) (i 2))
                                    (pi1 (dec x1 (sk (N 2))))
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x2) (i 2))
                                       (pi1 (dec x2 (sk (N 2))))
                                       (if_then_else_M
                                          (EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x3) (i 2))
                                          (pi1 (dec x3 (sk (N 2))))
                                          (if_then_else_M
                                             ((((EQ_M (reveal x4) (i 1)) &
                                                (EQ_M (to x2) (i 1))) &
                                               (EQ_M (to x1) (i 1))) &
                                              (notb (EQ_M (act x2) new))) &
                                             (EQ_M (act x1) new)
                                             (pi1 (dec x2 (sk (N 1))))
                                             (if_then_else_M
                                                ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                  (EQ_M (to x1) (i 1))) &
                                                 (notb (EQ_M (act x3) new))) &
                                                (EQ_M (act x1) new)
                                                (pi1 (dec x3 (sk (N 1))))
                                                (if_then_else_M
                                                  ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                  (EQ_M (to x2) (i 1))) &
                                                  (notb (EQ_M (act x3) new))) &
                                                  (EQ_M (act x2) new)
                                                  (pi1 (dec x3 (sk (N 1)))) O))))))
                                 O)))).
simpl. 
repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc (N 3))) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x3) (i 1))) (m3:=    (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x1) (i 2))
                                    (pi1 (dec x1 (sk (N 2))))
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x2) (i 2))
                                       (pi1 (dec x2 (sk (N 2))))
                                       (if_then_else_M
                                          (EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x3) (i 2))
                                          (pi1 (dec x3 (sk (N 2))))
                                          (if_then_else_M
                                             ((((EQ_M (reveal x4) (i 1)) &
                                                (EQ_M (to x2) (i 1))) &
                                               (EQ_M (to x1) (i 1))) &
                                              (notb (EQ_M (act x2) new))) &
                                             (EQ_M (act x1) new)
                                             (pi1 (dec x2 (sk (N 1))))
                                             (if_then_else_M
                                                ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                  (EQ_M (to x1) (i 1))) &
                                                 (notb (EQ_M (act x3) new))) &
                                                (EQ_M (act x1) new)
                                                (pi1 (dec x3 (sk (N 1))))
                                                (if_then_else_M
                                                  ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                  (EQ_M (to x2) (i 1))) &
                                                  (notb (EQ_M (act x3) new))) &
                                                  (EQ_M (act x2) new)
                                                  (pi1 (dec x3 (sk (N 1)))) O))))))).
simpl.

repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc (N 3))) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x2) (i 1))) (m3:=  (if_then_else_M
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)
      (if_then_else_M (EQ_M (reveal x4) (i 2)) O
         (if_then_else_M (EQ_M (to x4) (i 2))
            (enc (pi1 (dec x4 (sk (N 2))), ((nc (N 4)), pk (N 2)))
               (pi2 (dec x4 (sk (N 2)))) (sr 9)) O))
      (if_then_else_M (EQ_M (reveal x3) (i 2)) O
         (if_then_else_M (EQ_M (to x3) (i 2))
            (if_then_else_M
               (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
               (EQ_M (pi1 (dec x2 (sk (N 2)))) (nc (N 3))) 
               (nc 5)
               (if_then_else_M
                  (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                       (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                     (notb (EQ_M (act x3) new))) & 
                    (EQ_M (act x1) new)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
                  (EQ_M (pi1 (dec x2 (sk (N 2)))) (nc (N 3))) 
                  (nc 5)
                  (if_then_else_M
                     (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                     (pi1 (dec x1 (sk (N 2))))
                     (if_then_else_M
                        (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2))
                        (pi1 (dec x2 (sk (N 2))))
                        (if_then_else_M
                           (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
                           (pi1 (dec x3 (sk (N 2))))
                           (if_then_else_M
                              ((((EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x2) (i 1))) & 
                                (EQ_M (to x1) (i 1))) &
                               (notb (EQ_M (act x2) new))) &
                              (EQ_M (act x1) new) (pi1 (dec x2 (sk (N 1))))
                              (if_then_else_M
                                 ((((EQ_M (reveal x4) (i 1)) &
                                    (EQ_M (to x3) (i 1))) &
                                   (EQ_M (to x1) (i 1))) &
                                  (notb (EQ_M (act x3) new))) &
                                 (EQ_M (act x1) new)
                                 (pi1 (dec x3 (sk (N 1))))
                                 (if_then_else_M
                                    ((((EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x3) (i 1))) &
                                      (EQ_M (to x2) (i 1))) &
                                     (notb (EQ_M (act x3) new))) &
                                    (EQ_M (act x2) new)
                                    (pi1 (dec x3 (sk (N 1)))) O)))))))) O)))). 
simpl. 

repeat rewrite  EQ_BRmsg_msg' with (m1 := (pi1 (dec x2 (sk (N 1)))) ) (m2:= (nc (N 3))) (m:= (pi1 (dec x2 (sk (N 1)))) ) (b:=  (EQ_M (to x3) (i 1))) (m3:=  (if_then_else_M
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
      (EQ_M (pi1 (dec x2 (sk (N 2)))) (nc (N 3))) (nc 5)
      (if_then_else_M
         (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (pi1 (dec x3 (sk (N 1)))) (nc (N 3)))) &
         (EQ_M (pi1 (dec x2 (sk (N 2)))) (nc (N 3))) (nc 5)
         (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
            (pi1 (dec x1 (sk (N 2))))
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2))
               (pi1 (dec x2 (sk (N 2))))
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
                  (pi1 (dec x3 (sk (N 2))))
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) (pi1 (dec x2 (sk (N 1))))
                     (if_then_else_M
                        ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                          (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x3) new))) &
                        (EQ_M (act x1) new) (pi1 (dec x3 (sk (N 1))))
                        (if_then_else_M
                           ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                             (EQ_M (to x2) (i 1))) &
                            (notb (EQ_M (act x3) new))) & 
                           (EQ_M (act x2) new) (pi1 (dec x3 (sk (N 1)))) O))))))))). 
simpl.


(*assert((ostomsg t15) # (ostomsg t25)).
simpl. unfold qb10_ss, qb01_ss. unfold qb11_s. unfold qa12. unfold qa02_s.*)
 (*qb20_s qb21*)


apply  IFBRANCH_M4 with (ml1:=[msg (pk (N 1)); msg (pk (N 2))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2))]); try  reflexivity;  simpl.
apply  IFBRANCH_M4 with (ml1:=[msg (pk (N 1)); msg (pk (N 2)) ; bol (EQ_M (reveal x1) (i 1))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)) ; bol (EQ_M (reveal x1) (i 1))]); try  reflexivity;  simpl. 
apply  IFBRANCH_M4 with (ml1:=[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2))]) ;try  reflexivity;  simpl. 

apply  IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1))]); try  reflexivity;  simpl. 

apply  IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1))]); try  reflexivity;  simpl. 
apply  IFBRANCH_M3 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2))]); try  reflexivity;  simpl. 

apply  IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)))]); try  reflexivity;  simpl. 
apply  IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse)]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse)]); try  reflexivity;  simpl. 


apply  IFBRANCH_M2 with (ml1:= [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2))]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2))]); try  reflexivity;  simpl. 
apply  IFBRANCH_M1 with (ml1:=[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2)); bol (EQ_M (to (f mphi2)) (i 2));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), ((nc (N 4)), pi1 (k (N 2))))
         (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (rs (N 1)))]) (ml2 :=[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2)); bol (EQ_M (to (f mphi2)) (i 2));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), ((nc (N 4)), pi1 (k (N 2))))
         (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (rs (N 1)))]); try  reflexivity;  simpl. 
Focus 2.  
apply   IFBRANCH_M1 with (ml1:=[msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2)); bol (EQ_M (to (f mphi2)) (i 2));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), ((nc (N 4)), pi1 (k (N 2))))
         (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (rs (N 1)));
    bol
      (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
         (EQ_M (to (f mphi0)) (i 2)) FAlse)]) (ml2 := [msg (pk (N 1)); msg (pk (N 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (enc ((nc (N 3)), pk (N 1)) (pk (N 2)) (sr 1));
    bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (pi1 (dec x2 (sk (N 1)))) (nc (N 3))) & (EQ_M (to x2) (i 1));
    msg
      (enc (pi1 (pi2 (dec (f mphi1) (pi2 (k (N 1))))))
         (pi2 (pi2 (dec (f mphi1) (pi2 (k (N 1)))))) 
         (rs (N 1)));
    bol
      (if_then_else_B
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
                  (EQ_M (to (f mphi1)) (i 1)) FAlse)
               (EQ_M (to (f mphi0)) (i 1)) FAlse)
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (EQ_M (act (f mphi0)) new) FAlse);
    bol (EQ_M (reveal (f mphi2)) (i 2)); bol (EQ_M (to (f mphi2)) (i 2));
    msg
      (enc (pi1 (dec (f mphi2) (pi2 (k (N 2)))), ((nc (N 4)), pi1 (k (N 2))))
         (pi2 (dec (f mphi2) (pi2 (k (N 2))))) (rs (N 1)));
    bol
      (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
         (EQ_M (to (f mphi0)) (i 2)) FAlse)]); try  reflexivity;  simpl. 


apply RESTR_rev with (ml1:= 
apply IFBRANCH_M1.
aply_breq_same.


repeat redg; repeat rewrite IFTFb.

aply_breq_same.
 repeat rewrite andB_elm'' with (b1 := (EQ_M (to x1) (i 1)))(b2:= (EQ_M (act x1) new)).
 false_to_sesns_all.
aply_breq. 
repeat redg; repeat rewrite IFTFb.
 false_to_sesns_all.
aply_breq. 
repeat redg; repeat rewrite IFTFb.
aply_breq. 

repeat redg; repeat rewrite IFTFb. 
 aply_breq_same.
 repeat rewrite andB_elm'' with (b1 := (EQ_M (to (f mphi1)) (i 1)))(b2:=  (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (nc (N 3)))).
false_to_sesns_all. 
aply_breq.
repeat redg; repeat rewrite IFTFb. 
pose proof(EQ_BRmsg_msg''). 

rewrite EQ_BRmsg_msg''' with (m1 := (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m2:= (nc (N 3))) (m:= (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m3:=  (if_then_else_M
         (if_then_else_B (EQ_M (reveal (f mphi2)) (i 1))
            (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse)
         (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2)) O
            (if_then_else_M (EQ_M (to (f mphi3)) (i 2))
               (enc
                  (pi1 (dec (f mphi3) (pi2 (k (N 2)))),
                  ((nc (N 4)), pi1 (k (N 2))))
                  (pi2 (dec (f mphi3) (pi2 (k (N 2))))) 
                  (rs (N 1))) O))
         (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2)) O
            (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
               (if_then_else_M
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                     (EQ_M (to (f mphi2)) (i 2)) FAlse)
                  (pi1 (dec (f mphi2) (pi2 (k (N 2)))))
                  (if_then_else_M
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                        FAlse) (pi1 (dec (f mphi1) (pi2 (k (N 1)))))
                     (if_then_else_M
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi2)) (i 1)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                              TRue) FAlse)
                        (pi1 (dec (f mphi2) (pi2 (k (N 1)))))
                        (if_then_else_M
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi2)) (i 1)) FAlse)
                                 (if_then_else_B (EQ_M (act (f mphi2)) new)
                                    FAlse TRue) FAlse)
                              (EQ_M (act (f mphi1)) new) FAlse)
                           (pi1 (dec (f mphi2) (pi2 (k (N 1))))) O)))) O))))  .
simpl. 
repeat redg; repeat rewrite IFTFb.

aply_breq.
false_to_sesns_all. 
aply_breq. 
false_to_sesns_all. 
aply_breq. 
repeat redg; repeat rewrite IFTFb.
repeat rewrite andB_elm'' with (b1 := (EQ_M (to (f mphi2)) (i 1)))(b2:=  (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 1))))) (nc (N 3)))).
false_to_sesns_all. simpl. 

aply_breq.

repeat redg; repeat rewrite IFTFb.
 rewrite EQ_BRmsg_msg''' with (m1 := (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m2:= (nc (N 3))) (m:= (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m3:= (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
         (pi1 (dec (f mphi1) (pi2 (k (N 2)))))
         (if_then_else_M
            (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) FAlse)
            (pi1 (dec (f mphi2) (pi2 (k (N 1))))) O))). simpl. 
 rewrite EQ_BRmsg_msg''' with (m1 := (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m2:= (nc (N 3))) (m:= (pi1 (dec (f mphi1) (pi2 (k (N 1))))) ) (m3:=  (if_then_else_M
           (if_then_else_B
              (if_then_else_B
                 (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse)
                 (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc (N 3))) FAlse)
              (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc (N 3))) FAlse)
           (nc 5)
           (if_then_else_M
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse)
                    (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc (N 3))) FAlse)
                 (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc (N 3))) FAlse)
              (nc 5)
              (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
                 (pi1 (dec (f mphi1) (pi2 (k (N 2)))))
                 (if_then_else_M
                    (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (pi1 (dec (f mphi2) (pi2 (k (N 1))))) O))))).  simpl. 
aply_breq. 
false_to_sesns_all.  simpl. 
rewrite andB_assoc with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b3:= (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc (N 3)))).

rewrite andB_assoc with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:=  ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
            (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc (N 3))))) (b3:= (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc (N 3)))).
rewrite andB_elm'' with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:=  (((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
          (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc (N 3)))) &
         (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc (N 3)))) ). 
false_to_sesns_all. simpl. 


aply_breq. 
repeat redg; repeat rewrite IFTFb.
rewrite <- IFSAME_M with (b:= (if_then_else_B
           (if_then_else_B
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
              (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc (N 3))) FAlse)
           (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc (N 3))) FAlse))  at 1. 
 repeat rewrite andB_elm'' with (b1:= (if_then_else_B
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
            (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc (N 3))) FAlse)) (b2:=  (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc (N 3)))).
repeat rewrite andB_elm'' with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:= (EQ_M (pi1 (dec (f mphi2) (pi2 (k (N 1))))) (nc (N 3)))).
aply_breq. 
aply_breq. 
rewrite <- IFSAME_M with (b:= (EQ_M (pi1 (dec (f mphi1) (pi2 (k (N 2))))) (nc (N 3))))  at 1.
aply_breq. 
Focus 3.  
false_to_sesns_all.  simpl. 
 aply_breq.  
repeat redg; repeat rewrite IFTFb. reflexivity. 
simpl. 

aply_breq_same.
assert(qa10_ss # qb10_ss).

repeat unf.
assert(qa01_ss # qb01_ss).
repeat unf.
 

apply breq_msgeq1'. simpl.

aply_breq_same.
