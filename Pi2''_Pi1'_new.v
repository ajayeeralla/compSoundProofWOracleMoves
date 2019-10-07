Load "Pi1_Pi2''".

Theorem pi2''_pi2': phi34 ~ phi44.

Proof.  repeat unf_phi. simpl. repeat unf_trm.
 (******************thn***************************)
 
assert(thn: qc10_ss # qd10_ss).
(******assert(thn: qc01_ss # qd01_ss).****)


 
unf.
repeat unf_qc ; repeat unf_qd.


 
assert (then_1:  (if_then_else_M (EQ_M (to x3) (i 2))
                     (if_then_else_M
                        (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                             (EQ_M (to x2) (i 2))) & 
                            (EQ_M (to x1) (i 1))) &
                           (notb (EQ_M (act x3) new))) & 
                          (EQ_M (act x1) new)) & (EQ_M (m x2) (grn 1))) &
                        (EQ_M (m x3) (grn 2)) mx2rn2
                        (if_then_else_M
                           (((((((EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x3) (i 1))) & 
                                (EQ_M (to x2) (i 2))) & 
                               (EQ_M (to x1) (i 1))) &
                              (notb (EQ_M (act x3) new))) &
                             (EQ_M (act x1) new)) & 
                            (EQ_M (m x2) (grn 1))) & 
                           (EQ_M (m x3) (grn 2)) mx3rn1
                           (if_then_else_M
                              (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                              mx1rn2
                              (if_then_else_M
                                 (EQ_M (reveal x4) (i 2)) &
                                 (EQ_M (to x3) (i 2)) mx3rn2
                                 (if_then_else_M
                                    ((((EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x2) (i 1))) &
                                      (EQ_M (to x1) (i 1))) &
                                     (notb (EQ_M (act x2) new))) &
                                    (EQ_M (act x1) new) mx2rn1 O))))) O) #  (if_then_else_M (EQ_M (to x3) (i 2))
                       (if_then_else_M
                          (((((((EQ_M (reveal x4) (i 2)) &
                                (EQ_M (to x3) (i 1))) & 
                               (EQ_M (to x2) (i 2))) & 
                              (EQ_M (to x1) (i 1))) &
                             (notb (EQ_M (act x3) new))) &
                            (EQ_M (act x1) new)) & 
                           (EQ_M (m x2) (grn 1))) & 
                          (EQ_M (m x3) (grn 2)) grn21
                          (if_then_else_M
                             (((((((EQ_M (reveal x4) (i 1)) &
                                   (EQ_M (to x3) (i 1))) &
                                  (EQ_M (to x2) (i 2))) &
                                 (EQ_M (to x1) (i 1))) &
                                (notb (EQ_M (act x3) new))) &
                               (EQ_M (act x1) new)) & 
                              (EQ_M (m x2) (grn 1))) & 
                             (EQ_M (m x3) (grn 2)) grn21
                             (if_then_else_M
                                (EQ_M (reveal x4) (i 2)) &
                                (EQ_M (to x1) (i 2)) mx1rn2
                                (if_then_else_M
                                   (EQ_M (reveal x4) (i 2)) &
                                   (EQ_M (to x3) (i 2)) mx3rn2
                                   (if_then_else_M
                                      ((((EQ_M (reveal x4) (i 1)) &
                                         (EQ_M (to x2) (i 1))) &
                                        (EQ_M (to x1) (i 1))) &
                                       (notb (EQ_M (act x2) new))) &
                                      (EQ_M (act x1) new) mx2rn1 O))))) O)).

 



assert(then_2 :   (if_then_else_M
            (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) mx3rn1
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
               mx1rn2
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn2
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1 O)))) #   (if_then_else_M
                             (((((((EQ_M (reveal x4) (i 1)) &
                                   (EQ_M (to x3) (i 1))) &
                                  (EQ_M (to x2) (i 2))) &
                                 (EQ_M (to x1) (i 1))) &
                                (notb (EQ_M (act x3) new))) &
                               (EQ_M (act x1) new)) & 
                              (EQ_M (m x2) (grn 1))) & 
                             (EQ_M (m x3) (grn 2)) grn21
                             (if_then_else_M
                                (EQ_M (reveal x4) (i 2)) &
                                (EQ_M (to x1) (i 2)) mx1rn2
                                (if_then_else_M
                                   (EQ_M (reveal x4) (i 2)) &
                                   (EQ_M (to x3) (i 2)) mx3rn2
                                   (if_then_else_M
                                      ((((EQ_M (reveal x4) (i 1)) &
                                         (EQ_M (to x2) (i 1))) &
                                        (EQ_M (to x1) (i 1))) &
                                       (notb (EQ_M (act x2) new))) &
                                      (EQ_M (act x1) new) mx2rn1 O))))).

rewrite andB_comm.
 unfold andB at 1.


pose proof(IFMORPH_M2 0  ((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
             (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
           (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
         (EQ_M (m x2) (grn 1)) FAlse mx3rn1
      (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2)) mx1rn2
         (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
            mx3rn2
            (if_then_else_M
               ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                 (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
               (EQ_M (act x1) new) mx2rn1 O)))).
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x3)  (grn 2) )) in H. simpl in H.
rewrite H.
clear H.




pose proof (EQBRmsg_msg   (if_then_else_M
         ((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
             (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
           (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
         (EQ_M (m x2) (grn 1)) (exp (G 0) (Mvar 2) (r 1))
         (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
            mx1rn2
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
               mx3rn2
               (if_then_else_M
                  ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                    (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                  (EQ_M (act x1) new) mx2rn1 O))))
      (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2)) mx1rn2
         (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
            mx3rn2
            (if_then_else_M
               ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                 (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
               (EQ_M (act x1) new) mx2rn1 O)))  0 1 2).
simpl in H.
pose proof(Forall_ELM_EVAL_M1).
apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x3) ) in H. simpl in H.
 
apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn2 ) in H.  simpl in H.
rewrite  H. clear H.
redg.
   reflexivity.
rewrite then_2 . clear then_2.
 
unfold andB at 7.
rewrite IFMORPH_M2' with (b:= (EQ_M (m x3) (grn 2))).

rewrite  IFFALSE_M .
rewrite EQBRmsg_msg' with (t1:= (m x3)) (t2:= (grn 2))  (t3:=  (if_then_else_M
           ((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
               (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
             (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
           (EQ_M (m x2) (grn 1)) grn21
           (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
              mx1rn2
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
                 mx3rn2
                 (if_then_else_M
                    ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                      (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                    (EQ_M (act x1) new) mx2rn1 O)))))  (t5:= (m x3)).

 reflexivity.
rewrite then_2 . clear then_2.

assert(then_3 :   (if_then_else_M
         (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) mx2rn2
         (if_then_else_M
            (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
               mx1rn2
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn2
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1 O)))))  #    (if_then_else_M
           (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
            (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
           (if_then_else_M
              (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                   (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                 (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
               (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                 mx1rn2
                 (if_then_else_M
                    (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn2
                    (if_then_else_M
                       ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                         (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                       (EQ_M (act x1) new) mx2rn1 O)))))).

rewrite andB_comm with (b2:= (EQ_M (m x2) (grn 1) ) ) .
aply_assoc.

 unfold andB at 1.
rewrite IFMORPH_M2'.

redg.
unfold mx2rn2.
pose proof (EQBRmsg_msg    (if_then_else_M
         ((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
             (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
           (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
         (EQ_M (m x3) (grn 2)) (exp (G 0) (Mvar 2) (r 2))
         (if_then_else_M
            (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
               mx1rn2
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn2
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1 O)))))
      (if_then_else_M
         (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
         (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
            mx1rn2
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
               mx3rn2
               (if_then_else_M
                  ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                    (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                   (EQ_M (act x1) new) mx2rn1 O))))  0 1 2).

pose proof(Forall_ELM_EVAL_M1).  
apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x2) ) in H. 
 

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn 1 ) in H.
simpl in H.
red_in H. simpl in H.
rewrite  H. clear H.

  
 
unfold andB at 1.
rewrite IFMORPH_M2' with (b:= (EQ_M (m x2) (grn 1))).

rewrite  IFFALSE_M .
rewrite commexp. redg.
 reflexivity.
rewrite then_2 . clear then_2.
assert(then3:  (if_then_else_M
         (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) mx2rn2
         (if_then_else_M
            (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
               mx1rn2
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn2
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1 O))))) #  (if_then_else_M
           (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
            (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
           (if_then_else_M
              (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                   (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                 (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
               (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                 mx1rn2
                 (if_then_else_M
                    (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn2
                    (if_then_else_M
                       ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                         (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                       (EQ_M (act x1) new) mx2rn1 O)))))).

aply_assoc.
rewrite andB_comm with (b1:= (EQ_M (m x2) (grn 1))).
rewrite <- andB_assoc .
rewrite <- andB_comm with (b1:= (EQ_M (m x2) (grn 1))).
unfold andB at 1 21 .
rewrite IFMORPH_M2' with (b:=  (EQ_M (m x2) (grn 1))).
rewrite IFMORPH_M2' with (b:=  (EQ_M (m x2) (grn 1))).
redg. redg.
unfold mx2rn2.

pose proof (EQBRmsg_msg    (if_then_else_M
         ((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
             (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
           (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
         (EQ_M (m x3) (grn 2)) (exp (G 0) (Mvar 2) (r 2))
         (if_then_else_M
            (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
               mx1rn2
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn2
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1 O)))))
      (if_then_else_M
         (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
         (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
            mx1rn2
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
               mx3rn2
               (if_then_else_M
                  ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                    (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                  (EQ_M (act x1) new) mx2rn1 O)))) 0 1 2 ).
pose proof(Forall_ELM_EVAL_M1).
apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x2) ) in H. simpl in H.
 
apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn 1 ) in H. simpl in H.
rewrite  H. clear H.
rewrite commexp.
redg. simpl.


pose proof (EQBRmsg_msg  (if_then_else_M
           ((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
               (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
             (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
           (EQ_M (m x3) (grn 2)) grn21
           (if_then_else_M
              (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                   (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                 (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
               (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                 mx1rn2
                 (if_then_else_M
                    (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn2
                    (if_then_else_M
                       ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                         (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                       (EQ_M (act x1) new) mx2rn1 O)))))
        (if_then_else_M
           (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
            (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) grn21
           (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
              mx1rn2
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
                 mx3rn2
                 (if_then_else_M
                    ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                      (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                    (EQ_M (act x1) new) mx2rn1 O))))  0 1 2).


apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x2) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn 1 ) in H.
  simpl in H.

rewrite  H. clear H.

reflexivity.
pose proof(andB_assoc 0 1 2) .

pose proof(andB_comm 0 1).
apply Forall_ELM_EVAL_B with (n:= 1) (b:= ((Bvar 1) & (Bvar 2))) in H0. simpl in H0.
rewrite H0 in H; clear H0.
pose proof(andB_assoc 1 2 0).

rewrite <-H0 in H. clear H0.
apply Forall_ELM_EVAL_B with (n:= 1) (b:=  (EQ_M (m x2) grn1)) in H.
apply Forall_ELM_EVAL_B with (n:= 0) (b:= ((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) in H. 
apply Forall_ELM_EVAL_B with (n:= 2) (b:= (EQ_M (m x3) grn2)) in H.
 simpl in H.
rewrite <- H.
clear H.



pose proof(IFMORPH_M2 0  (if_then_else_B (EQ_M (m x3) grn2)
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 1)) FAlse)
                           (EQ_M (to (f mphi1)) (i 2)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
         mx2rn2
         (if_then_else_M
            (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
               mx1rn1
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn3
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1 O)))) ) . 
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x2) grn1) ) in H. simpl in H.
rewrite H.
clear H.

redg.

pose proof (EQBRmsg_msg  (if_then_else_M
            (if_then_else_B
               (EQ_M (m (f mphi2))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 1)) FAlse)
                           (EQ_M (to (f mphi1)) (i 2)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse)
            (exp (pi1 (ggen (N 0))) (Mvar 2) (rr (N 2)))
            (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi2)) (i 1)) FAlse)
                                 (EQ_M (to (f mphi1)) (i 2)) FAlse)
                              (EQ_M (to (f mphi0)) (i 1)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (EQ_M (m (f mphi1))
                        (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                     FAlse)
                  (EQ_M (m (f mphi2))
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
                  FAlse)
               (exp (pi1 (ggen (N 0)))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))
                  (rr (N 1)))
               (if_then_else_M
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                     (EQ_M (to (f mphi0)) (i 2)) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 1)))
                  (if_then_else_M
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                        (EQ_M (to (f mphi2)) (i 2)) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 3)))
                     (if_then_else_M
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                 (EQ_M (to (f mphi0)) (i 1)) FAlse)
                              (if_then_else_B (EQ_M (act (f mphi1)) new)
                                 FAlse TRue) FAlse)
                           (EQ_M (act (f mphi0)) new) FAlse)
                        (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O)))))     (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                 (EQ_M (to (f mphi2)) (i 1)) FAlse)
                              (EQ_M (to (f mphi1)) (i 2)) FAlse)
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (EQ_M (m (f mphi1))
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                  FAlse)
               (EQ_M (m (f mphi2))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
               FAlse)
            (exp (pi1 (ggen (N 0)))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))
               (rr (N 1)))
            (if_then_else_M
               (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                  (EQ_M (to (f mphi0)) (i 2)) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 1)))
               (if_then_else_M
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                     (EQ_M (to (f mphi2)) (i 2)) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 3)))
                  (if_then_else_M
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                 (EQ_M (to (f mphi1)) (i 1)) FAlse)
                              (EQ_M (to (f mphi0)) (i 1)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O)))) 0 1 2).


apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x2) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn1 ) in H. simpl in H.
rewrite  H. clear H.



pose proof(IFMORPH_M2 0   (if_then_else_B (EQ_M (m x3) grn2)
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B
                             (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                                (EQ_M (to (f mphi2)) (i 1)) FAlse)
                             (EQ_M (to (f mphi1)) (i 2)) FAlse)
                          (EQ_M (to (f mphi0)) (i 1)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
           grn21
           (if_then_else_M
              (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                   (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                 (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
               (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                 mx1rn1
                 (if_then_else_M
                    (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn3
                    (if_then_else_M
                       ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                         (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                       (EQ_M (act x1) new) mx2rn1 O))))) .
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x2) grn1) ) in H.
simpl in H. red_in H.
rewrite H.   rewrite <-commexp.
 
reflexivity.  rewrite then_1. clear then_1.

assert(H1:   (if_then_else_M
                     (EQ_M (reveal x3) (i 2)) & (EQ_M (to x1) (i 2))
                     (if_then_else_M
                        (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 2))) &
                             (EQ_M (to x2) (i 1))) & 
                            (EQ_M (to x1) (i 2))) &
                           (notb (EQ_M (act x3) new))) & 
                          (EQ_M (act x1) new)) & (EQ_M (m x2) grn1)) &
                        (EQ_M (m x3) grn2) mx2rn2
                        (if_then_else_M
                           (((((((EQ_M (reveal x4) (i 2)) &
                                 (EQ_M (to x3) (i 2))) & 
                                (EQ_M (to x2) (i 1))) & 
                               (EQ_M (to x1) (i 2))) &
                              (notb (EQ_M (act x3) new))) &
                             (EQ_M (act x1) new)) & 
                            (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) mx3rn1
                           (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                              (if_then_else_M (EQ_M (to x4) (i 1)) acc O))))
                     (if_then_else_M
                        (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2))
                        (if_then_else_M
                           (((((((EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x3) (i 2))) & 
                                (EQ_M (to x2) (i 1))) & 
                               (EQ_M (to x1) (i 2))) &
                              (notb (EQ_M (act x3) new))) &
                             (EQ_M (act x1) new)) & 
                            (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) mx2rn2
                           (if_then_else_M
                              (((((((EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x3) (i 2))) &
                                   (EQ_M (to x2) (i 1))) &
                                  (EQ_M (to x1) (i 2))) &
                                 (notb (EQ_M (act x3) new))) &
                                (EQ_M (act x1) new)) & 
                               (EQ_M (m x2) grn1)) & 
                              (EQ_M (m x3) grn2) mx3rn1
                              (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                                 (if_then_else_M (EQ_M (to x4) (i 1)) acc O))))
                        (if_then_else_M (EQ_M (to x3) (i 1))
                           (if_then_else_M
                              (((((((EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x3) (i 1))) &
                                   (EQ_M (to x2) (i 2))) &
                                  (EQ_M (to x1) (i 1))) &
                                 (notb (EQ_M (act x3) new))) &
                                (EQ_M (act x1) new)) & 
                               (EQ_M (m x2) grn1)) & 
                              (EQ_M (m x3) grn2) mx2rn2
                              (if_then_else_M
                                 (((((((EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x3) (i 1))) &
                                      (EQ_M (to x2) (i 2))) &
                                     (EQ_M (to x1) (i 1))) &
                                    (notb (EQ_M (act x3) new))) &
                                   (EQ_M (act x1) new)) & 
                                  (EQ_M (m x2) grn1)) & 
                                 (EQ_M (m x3) grn2) mx3rn1
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x1) (i 2)) mx1rn1
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x3) (i 2)) mx3rn3
                                       (if_then_else_M
                                          ((((EQ_M (reveal x4) (i 1)) &
                                             (EQ_M (to x2) (i 1))) &
                                            (EQ_M (to x1) (i 1))) &
                                           (notb (EQ_M (act x2) new))) &
                                          (EQ_M (act x1) new) mx2rn1 O))))) O)))
              #  (if_then_else_M
                       (EQ_M (reveal x3) (i 2)) & (EQ_M (to x1) (i 2))
                       (if_then_else_M
                          (((((((EQ_M (reveal x4) (i 1)) &
                                (EQ_M (to x3) (i 2))) & 
                               (EQ_M (to x2) (i 1))) & 
                              (EQ_M (to x1) (i 2))) &
                             (notb (EQ_M (act x3) new))) &
                            (EQ_M (act x1) new)) & 
                           (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
                          (if_then_else_M
                             (((((((EQ_M (reveal x4) (i 2)) &
                                   (EQ_M (to x3) (i 2))) &
                                  (EQ_M (to x2) (i 1))) &
                                 (EQ_M (to x1) (i 2))) &
                                (notb (EQ_M (act x3) new))) &
                               (EQ_M (act x1) new)) & 
                              (EQ_M (m x2) grn1)) & 
                             (EQ_M (m x3) grn2) grn21
                             (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                                (if_then_else_M (EQ_M (to x4) (i 1)) acc O))))
                       (if_then_else_M
                          (EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2))
                          (if_then_else_M
                             (((((((EQ_M (reveal x4) (i 1)) &
                                   (EQ_M (to x3) (i 2))) &
                                  (EQ_M (to x2) (i 1))) &
                                 (EQ_M (to x1) (i 2))) &
                                (notb (EQ_M (act x3) new))) &
                               (EQ_M (act x1) new)) & 
                              (EQ_M (m x2) grn1)) & 
                             (EQ_M (m x3) grn2) grn21
                             (if_then_else_M
                                (((((((EQ_M (reveal x4) (i 2)) &
                                      (EQ_M (to x3) (i 2))) &
                                     (EQ_M (to x2) (i 1))) &
                                    (EQ_M (to x1) (i 2))) &
                                   (notb (EQ_M (act x3) new))) &
                                  (EQ_M (act x1) new)) & 
                                 (EQ_M (m x2) grn1)) & 
                                (EQ_M (m x3) grn2) grn21
                                (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                                   (if_then_else_M (EQ_M (to x4) (i 1)) acc O))))
                          (if_then_else_M (EQ_M (to x3) (i 1))
                             (if_then_else_M
                                (((((((EQ_M (reveal x4) (i 2)) &
                                      (EQ_M (to x3) (i 1))) &
                                     (EQ_M (to x2) (i 2))) &
                                    (EQ_M (to x1) (i 1))) &
                                   (notb (EQ_M (act x3) new))) &
                                  (EQ_M (act x1) new)) & 
                                 (EQ_M (m x2) grn1)) & 
                                (EQ_M (m x3) grn2) grn21
                                (if_then_else_M
                                   (((((((EQ_M (reveal x4) (i 1)) &
                                         (EQ_M (to x3) (i 1))) &
                                        (EQ_M (to x2) (i 2))) &
                                       (EQ_M (to x1) (i 1))) &
                                      (notb (EQ_M (act x3) new))) &
                                     (EQ_M (act x1) new)) &
                                    (EQ_M (m x2) grn1)) & 
                                   (EQ_M (m x3) grn2) grn21
                                   (if_then_else_M
                                      (EQ_M (reveal x4) (i 2)) &
                                      (EQ_M (to x1) (i 2)) mx1rn1
                                      (if_then_else_M
                                         (EQ_M (reveal x4) (i 2)) &
                                         (EQ_M (to x3) (i 2)) mx3rn3
                                         (if_then_else_M
                                            ((((EQ_M (reveal x4) (i 1)) &
                                               (EQ_M (to x2) (i 1))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x2) new))) &
                                            (EQ_M (act x1) new) mx2rn1 O)))))
                             O)))).




assert(H2:  (if_then_else_M
            (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) mx3rn1
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
               mx1rn1
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn3
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1 O)))) # (if_then_else_M
              (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                   (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                 (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
               (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                 mx1rn1
                 (if_then_else_M
                    (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn3
                    (if_then_else_M
                       ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                         (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                       (EQ_M (act x1) new) mx2rn1 O))))).
pose proof(andB_comm 0 1).

apply Forall_ELM_EVAL_B with (n:= 0) (b:= (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1))) in H.
apply Forall_ELM_EVAL_B with (n:= 1) (b:= (EQ_M (m x3) grn2)) in H. simpl in H.

rewrite H. clear H.

pose proof(IFMORPH_M2 0  (if_then_else_B
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 1)) FAlse)
                        (EQ_M (to (f mphi1)) (i 2)) FAlse)
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r 1))) FAlse) FAlse mx3rn1  (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2)) mx1rn1
         (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
            mx3rn3
            (if_then_else_M
               ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                 (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
               (EQ_M (act x1) new) mx2rn1 O))) ).
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x3) grn2) ) in H. simpl in H.
rewrite H.
clear H.

pose proof (EQBRmsg_msg   (if_then_else_M
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 1)) FAlse)
                        (EQ_M (to (f mphi1)) (i 2)) FAlse)
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r  1))) FAlse)
         (exp (pi1 (ggen (N 0))) (Mvar 2) (r 1))
         (if_then_else_M
            (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
               (EQ_M (to (f mphi0)) (i 2)) FAlse)
            (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r  1))
            (if_then_else_M
               (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                  (EQ_M (to (f mphi2)) (i 2)) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r 3))
               (if_then_else_M
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi1)) (i 1)) FAlse)
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r  1)) O))))  (if_then_else_M FAlse (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r  1))
         (if_then_else_M
            (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
               (EQ_M (to (f mphi0)) (i 2)) FAlse)
            (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r 1))
            (if_then_else_M
               (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                  (EQ_M (to (f mphi2)) (i 2)) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r 3))
               (if_then_else_M
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi1)) (i 1)) FAlse)
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r  1)) O)))) 0 1 2).

pose proof(Forall_ELM_EVAL_M1).
apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x3) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn2 ) in H. simpl in H.
rewrite  H. clear H.
repeat redg.



pose proof(IFMORPH_M2 0  (if_then_else_B
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 1)) FAlse)
                        (EQ_M (to (f mphi1)) (i 2)) FAlse)
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r  1))) FAlse) FAlse grn21  (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
           mx1rn1
           (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
              mx3rn3
              (if_then_else_M
                 ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                   (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                 (EQ_M (act x1) new) mx2rn1 O))) ).
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x3) grn2) ) in H. simpl in H.
rewrite H. clear H0 H. repeat redg. reflexivity.
rewrite H2. clear H2.


pose proof(andB_assoc 0 1 2) .

pose proof(andB_comm 0 1).
apply Forall_ELM_EVAL_B with (n:= 1) (b:= ((Bvar 1) & (Bvar 2))) in H0. simpl in H0.
rewrite H0 in H; clear H0.
pose proof(andB_assoc 1 2 0).

rewrite <-H0 in H. clear H0.
apply Forall_ELM_EVAL_B with (n:= 1) (b:=  (EQ_M (m x2) grn1)) in H.
apply Forall_ELM_EVAL_B with (n:= 0) (b:= ((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) in H. 
apply Forall_ELM_EVAL_B with (n:= 2) (b:= (EQ_M (m x3) grn2)) in H.
 simpl in H.
rewrite <- H.
clear H.



pose proof(IFMORPH_M2 0  (if_then_else_B (EQ_M (m x3) grn2)
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 1)) FAlse)
                           (EQ_M (to (f mphi1)) (i 2)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
         mx2rn2
         (if_then_else_M
            (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
               mx1rn1
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn3
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1 O)))) ) . 
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x2) grn1) ) in H. simpl in H.
rewrite H.
clear H.

repeat redg.

pose proof (EQBRmsg_msg  (if_then_else_M
            (if_then_else_B
               (EQ_M (m (f mphi2))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 1)) FAlse)
                           (EQ_M (to (f mphi1)) (i 2)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse)
            (exp (pi1 (ggen (N 0))) (Mvar 2) (rr (N 2)))
            (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi2)) (i 1)) FAlse)
                                 (EQ_M (to (f mphi1)) (i 2)) FAlse)
                              (EQ_M (to (f mphi0)) (i 1)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (EQ_M (m (f mphi1))
                        (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                     FAlse)
                  (EQ_M (m (f mphi2))
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
                  FAlse)
               (exp (pi1 (ggen (N 0)))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))
                  (rr (N 1)))
               (if_then_else_M
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                     (EQ_M (to (f mphi0)) (i 2)) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 1)))
                  (if_then_else_M
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                        (EQ_M (to (f mphi2)) (i 2)) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 3)))
                     (if_then_else_M
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                 (EQ_M (to (f mphi0)) (i 1)) FAlse)
                              (if_then_else_B (EQ_M (act (f mphi1)) new)
                                 FAlse TRue) FAlse)
                           (EQ_M (act (f mphi0)) new) FAlse)
                        (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O)))))     (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                 (EQ_M (to (f mphi2)) (i 1)) FAlse)
                              (EQ_M (to (f mphi1)) (i 2)) FAlse)
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (EQ_M (m (f mphi1))
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                  FAlse)
               (EQ_M (m (f mphi2))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
               FAlse)
            (exp (pi1 (ggen (N 0)))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))
               (rr (N 1)))
            (if_then_else_M
               (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                  (EQ_M (to (f mphi0)) (i 2)) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 1)))
               (if_then_else_M
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                     (EQ_M (to (f mphi2)) (i 2)) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 3)))
                  (if_then_else_M
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                 (EQ_M (to (f mphi1)) (i 1)) FAlse)
                              (EQ_M (to (f mphi0)) (i 1)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O)))) 0 1 2).


apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x2) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn1 ) in H. simpl in H.
rewrite  H. clear H.



pose proof(IFMORPH_M2 0   (if_then_else_B (EQ_M (m x3) grn2)
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B
                             (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                                (EQ_M (to (f mphi2)) (i 1)) FAlse)
                             (EQ_M (to (f mphi1)) (i 2)) FAlse)
                          (EQ_M (to (f mphi0)) (i 1)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
           grn21
           (if_then_else_M
              (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                   (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                 (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
               (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                 mx1rn1
                 (if_then_else_M
                    (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn3
                    (if_then_else_M
                       ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                         (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                       (EQ_M (act x1) new) mx2rn1 O))))) .
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x2) grn1) ) in H.
simpl in H. red_in H.
rewrite H.  clear H.
pose proof(andB_assoc 0 1 2) .

pose proof(andB_comm 0 1).
apply Forall_ELM_EVAL_B with (n:= 1) (b:= ((Bvar 1) & (Bvar 2))) in H0. simpl in H0.
rewrite H0 in H; clear H0.
pose proof(andB_assoc 1 2 0).

rewrite <-H0 in H. clear H0.
apply Forall_ELM_EVAL_B with (n:= 1) (b:=  (EQ_M (m x2) grn1)) in H.
apply Forall_ELM_EVAL_B with (n:= 0) (b:= ((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 2))) &
              (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) in H. 
apply Forall_ELM_EVAL_B with (n:= 2) (b:= (EQ_M (m x3) grn2)) in H.
 simpl in H. simpl.
rewrite <- H.
clear H.




pose proof(IFMORPH_M2 0   (if_then_else_B (EQ_M (m x3) grn2)
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi2)) (i 2)) FAlse)
                           (EQ_M (to (f mphi1)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 2)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
         mx2rn2
         (if_then_else_M
            (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
                 (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) mx3rn1
            (if_then_else_M (EQ_M (reveal x4) (i 1)) O
               (if_then_else_M (EQ_M (to x4) (i 1)) acc O)))).
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x2) grn1) ) in H. simpl in H.
repeat red_in H.
rewrite H.
clear H.

pose proof (EQBRmsg_msg    (if_then_else_M
            (if_then_else_B
               (EQ_M (m (f mphi2))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi2)) (i 2)) FAlse)
                           (EQ_M (to (f mphi1)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 2)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse)
            (exp (pi1 (ggen (N 0))) (Mvar 2) (rr (N 2)))
            (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 2))
                                    (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                 (EQ_M (to (f mphi1)) (i 1)) FAlse)
                              (EQ_M (to (f mphi0)) (i 2)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (EQ_M (m (f mphi1))
                        (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                     FAlse)
                  (EQ_M (m (f mphi2))
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
                  FAlse) (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
               (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                  (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O))))
         (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                                 (EQ_M (to (f mphi2)) (i 2)) FAlse)
                              (EQ_M (to (f mphi1)) (i 1)) FAlse)
                           (EQ_M (to (f mphi0)) (i 2)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (EQ_M (m (f mphi1))
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                  FAlse)
               (EQ_M (m (f mphi2))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
               FAlse) (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
            (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
               (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O))) 0 1 2).

pose proof(Forall_ELM_EVAL_M1).
apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x2) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn1 ) in H. simpl in H.
rewrite  H. clear H.
repeat redg.

pose proof(andB_comm 0 1).

apply Forall_ELM_EVAL_B with (n:= 0) (b:= (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1))) in H.
apply Forall_ELM_EVAL_B with (n:= 1) (b:= (EQ_M (m x3) grn2)) in H. simpl in H.

rewrite H. clear H.

pose proof(IFMORPH_M2 0  (if_then_else_B
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 1)) FAlse)
                        (EQ_M (to (f mphi1)) (i 2)) FAlse)
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r  1))) FAlse) FAlse grn21  (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
           mx1rn1
           (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
              mx3rn3
              (if_then_else_M
                 ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                   (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                 (EQ_M (act x1) new) mx2rn1 O))) ).
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x3) grn2) ) in H. simpl in H.
rewrite H. clear H0 H. repeat redg. 

pose proof(andB_comm 0 1).

apply Forall_ELM_EVAL_B with (n:= 0) (b:= (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
           (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1))) in H.
apply Forall_ELM_EVAL_B with (n:= 1) (b:= (EQ_M (m x3) grn2)) in H. simpl in H.

rewrite H. clear H.

pose proof(IFMORPH_M2 0    (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 2))
                                    (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                 (EQ_M (to (f mphi1)) (i 1)) FAlse)
                              (EQ_M (to (f mphi0)) (i 2)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (EQ_M (m (f mphi1))
                        (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                     FAlse) FAlse
               (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
               (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                  (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O))).
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x3) grn2) ) in H. simpl in H.
repeat red_in H.
rewrite H.
clear H.

pose proof(EQBRmsg_msg  (if_then_else_M
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 2))
                                    (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                 (EQ_M (to (f mphi1)) (i 1)) FAlse)
                              (EQ_M (to (f mphi0)) (i 2)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (EQ_M (m (f mphi1))
                        (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                     FAlse) (exp (pi1 (ggen (N 0))) (Mvar 2) (rr (N 1)))
                  (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                     (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O)))
               (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                  (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O)) 0 1 2).
pose proof(Forall_ELM_EVAL_M1).
apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x3) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn2 ) in H. simpl in H.
rewrite  H. clear H.
repeat redg.


pose proof(IFMORPH_M2 0  (if_then_else_B (EQ_M (m x3) grn2)
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B
                             (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                (EQ_M (to (f mphi2)) (i 2)) FAlse)
                             (EQ_M (to (f mphi1)) (i 1)) FAlse)
                          (EQ_M (to (f mphi0)) (i 2)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
           grn21
           (if_then_else_M
              (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
                   (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
                 (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
               (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
              (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                 (if_then_else_M (EQ_M (to x4) (i 1)) acc O)))).

apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x2) grn1) ) in H. simpl in H.
repeat red_in H.
rewrite H.
clear H.
clear H0.


pose proof(andB_comm 0 1).

apply Forall_ELM_EVAL_B with (n:= 0) (b:= (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
           (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1))) in H.
apply Forall_ELM_EVAL_B with (n:= 1) (b:= (EQ_M (m x3) grn2)) in H. simpl in H.

rewrite H. clear H.
pose proof(IFMORPH_M2 0  (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B
                             (if_then_else_B
                                (if_then_else_B
                                   (if_then_else_B
                                      (EQ_M (reveal (f mphi3)) (i 2))
                                      (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                   (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                (EQ_M (to (f mphi0)) (i 2)) FAlse)
                             (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                                TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                       (EQ_M (m (f mphi1))
                          (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0)))
                             (rr (N 1)))) FAlse) FAlse
                 (exp (pi1 (ggen (N 0)))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))
                    (rr (N 1)))
                 (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                    (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O))).

apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x3) grn2) ) in H. simpl in H.
repeat red_in H.
rewrite H.
clear H.

rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 1))) (y:= (rr (N 2))).  repeat redg.
reflexivity.

rewrite H1. clear H1. reflexivity.



(********************************************************************************************)
(*******************************************************************************************)


(**************************assert(e_then:  qc01_ss # qd01_ss*********************************************)
assert (e_then:  qc01_ss # qd01_ss).


repeat unf.


assert (e_then_1:   (if_then_else_M
                  (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 2))) &
                       (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
                     (notb (EQ_M (act x3) new))) & 
                    (EQ_M (act x1) new)) & (EQ_M (m x2) grn1)) &
                  (EQ_M (m x3) grn2) mx2rn2
                  (if_then_else_M
                     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
                          (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
                        (notb (EQ_M (act x3) new))) & 
                       (EQ_M (act x1) new)) & (EQ_M (m x2) grn1)) &
                     (EQ_M (m x3) grn2) mx3rn1
                     (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                        (if_then_else_M (EQ_M (to x4) (i 1)) acc O)))) #  (if_then_else_M
                    (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 2))) &
                         (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
                       (notb (EQ_M (act x3) new))) & 
                      (EQ_M (act x1) new)) & (EQ_M (m x2) grn1)) &
                    (EQ_M (m x3) grn2) grn21
                    (if_then_else_M
                       (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
                            (EQ_M (to x2) (i 1))) & 
                           (EQ_M (to x1) (i 2))) & 
                          (notb (EQ_M (act x3) new))) & 
                         (EQ_M (act x1) new)) & (EQ_M (m x2) grn1)) &
                       (EQ_M (m x3) grn2) grn21
                       (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                          (if_then_else_M (EQ_M (to x4) (i 1)) acc O)))) ).





pose proof(andB_comm 0 1).

apply Forall_ELM_EVAL_B with (n:= 0) (b:= (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
           (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1))) in H.
apply Forall_ELM_EVAL_B with (n:= 1) (b:= (EQ_M (m x3) grn2)) in H. simpl in H.

rewrite H. clear H.


pose proof(IFMORPH_M2 0    (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 2)) FAlse)
                           (EQ_M (to (f mphi1)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 2)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse)
               (EQ_M (m (f mphi1))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
               FAlse) FAlse mx3rn1
         (if_then_else_M (EQ_M (reveal x4) (i 1)) O
            (if_then_else_M (EQ_M (to x4) (i 1)) acc O))).
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x3) grn2) ) in H. simpl in H.
rewrite H.
clear H.

pose proof (EQBRmsg_msg   (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 2)) FAlse)
                           (EQ_M (to (f mphi1)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 2)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse)
               (EQ_M (m (f mphi1))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
               FAlse) (exp (pi1 (ggen (N 0))) (Mvar 2) (rr (N 1)))
            (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
               (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O)))   (if_then_else_M FAlse
            (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
            (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
               (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O)))  0 1 2).


apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x3) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn2 ) in H. simpl in H.
rewrite  H. clear H.






pose proof(andB_assoc 0 1 2) .

pose proof(andB_comm 0 1).
apply Forall_ELM_EVAL_B with (n:= 1) (b:= ((Bvar 1) & (Bvar 2))) in H0. simpl in H0.
rewrite H0 in H; clear H0.
pose proof(andB_assoc 1 2 0).

rewrite <-H0 in H. clear H0.
apply Forall_ELM_EVAL_B with (n:= 1) (b:=  (EQ_M (m x2) grn1)) in H.
apply Forall_ELM_EVAL_B with (n:= 0) (b:= ((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 2))) &
           (EQ_M (to x2) (i 1))) & (EQ_M (to x1) (i 2))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) in H. 
apply Forall_ELM_EVAL_B with (n:= 2) (b:= (EQ_M (m x3) grn2)) in H.
 simpl in H.
rewrite <- H.
clear H.



pose proof(IFMORPH_M2 0  (if_then_else_B (EQ_M (m x3) grn2)
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 2)) FAlse)
                        (EQ_M (to (f mphi1)) (i 1)) FAlse)
                     (EQ_M (to (f mphi0)) (i 2)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
      mx2rn2
      (if_then_else_M (EQ_M (m (f mphi2)) grn2)
         (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 2)) FAlse)
                           (EQ_M (to (f mphi1)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 2)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse)
               (EQ_M (m (f mphi1))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
               FAlse) (exp (pi1 (ggen (N 0))) grn2 (rr (N 1)))
            (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
               (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O)))
         (if_then_else_M FAlse
            (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
            (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
               (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O))))) . 
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x2) grn1) ) in H. simpl in H.
rewrite H.
clear H.

repeat redg.


pose proof (EQBRmsg_msg (if_then_else_M
         (if_then_else_B
            (EQ_M (m (f mphi2))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 2)) FAlse)
                        (EQ_M (to (f mphi1)) (i 1)) FAlse)
                     (EQ_M (to (f mphi0)) (i 2)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse)
         (exp (pi1 (ggen (N 0))) (Mvar 2) (rr (N 2)))
         (if_then_else_M
            (EQ_M (m (f mphi2))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
            (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                                 (EQ_M (to (f mphi2)) (i 2)) FAlse)
                              (EQ_M (to (f mphi1)) (i 1)) FAlse)
                           (EQ_M (to (f mphi0)) (i 2)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (EQ_M (m (f mphi1))
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                  FAlse)
               (exp (pi1 (ggen (N 0)))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))
                  (rr (N 1)))
               (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                  (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O)))
            (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
               (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O))))
      (if_then_else_M
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
         (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 2)) FAlse)
                           (EQ_M (to (f mphi1)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 2)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse)
               (EQ_M (m (f mphi1))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
               FAlse)
            (exp (pi1 (ggen (N 0)))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))
               (rr (N 1)))
            (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
               (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O)))
         (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
            (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O)))  0 1 2).

pose proof(Forall_ELM_EVAL_M1).
apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x2) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn1 ) in H. simpl in H.
rewrite  H. clear H.

pose proof(IFMORPH_M2 0    (if_then_else_B (EQ_M (m x3) grn2)
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                             (EQ_M (to (f mphi2)) (i 2)) FAlse)
                          (EQ_M (to (f mphi1)) (i 1)) FAlse)
                       (EQ_M (to (f mphi0)) (i 2)) FAlse)
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
        grn21
        (if_then_else_M
           (if_then_else_B (EQ_M (m x3) grn2)
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B
                             (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                                (EQ_M (to (f mphi2)) (i 2)) FAlse)
                             (EQ_M (to (f mphi1)) (i 1)) FAlse)
                          (EQ_M (to (f mphi0)) (i 2)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                 (EQ_M (m (f mphi1))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                 FAlse) FAlse) grn21
           (if_then_else_M (EQ_M (reveal x4) (i 1)) O
              (if_then_else_M (EQ_M (to x4) (i 1)) acc O)))).    
          
apply Forall_ELM_EVAL_M  with (n:= 0) (x:= (EQ_M (m x2) grn1) ) in H. simpl in H.  rewrite H.

 clear H.



 rewrite commexp.
repeat redg.
pose proof(IFMORPH_M2 0   (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B
                             (if_then_else_B
                                (if_then_else_B
                                   (EQ_M (reveal (f mphi3)) (i 2))
                                   (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                (EQ_M (to (f mphi1)) (i 1)) FAlse)
                             (EQ_M (to (f mphi0)) (i 2)) FAlse)
                          (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                             TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                    (EQ_M (m (f mphi1))
                       (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                    FAlse) FAlse
              (exp (pi1 (ggen (N 0)))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))
                 (rr (N 2)))
              (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                 (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O))).

apply Forall_ELM_EVAL_M  with (n:= 0) (x:= (EQ_M (m x3) grn2) ) in H. simpl in H.  rewrite H.

 clear H. repeat redg.

reflexivity.  rewrite e_then_1. 

assert(e_then_2:  (if_then_else_M (EQ_M (to x3) (i 1))
                        (if_then_else_M
                           (((((((EQ_M (reveal x4) (i 2)) &
                                 (EQ_M (to x3) (i 1))) & 
                                (EQ_M (to x2) (i 2))) & 
                               (EQ_M (to x1) (i 1))) &
                              (notb (EQ_M (act x3) new))) &
                             (EQ_M (act x1) new)) & 
                            (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) mx2rn2
                           (if_then_else_M
                              (((((((EQ_M (reveal x4) (i 1)) &
                                    (EQ_M (to x3) (i 1))) &
                                   (EQ_M (to x2) (i 2))) &
                                  (EQ_M (to x1) (i 1))) &
                                 (notb (EQ_M (act x3) new))) &
                                (EQ_M (act x1) new)) & 
                               (EQ_M (m x2) grn1)) & 
                              (EQ_M (m x3) grn2) mx3rn1
                              (if_then_else_M
                                 (EQ_M (reveal x4) (i 2)) &
                                 (EQ_M (to x1) (i 2)) mx1rn1
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x3) (i 2)) mx3rn3
                                    (if_then_else_M
                                       ((((EQ_M (reveal x4) (i 1)) &
                                          (EQ_M (to x2) (i 1))) &
                                         (EQ_M (to x1) (i 1))) &
                                        (notb (EQ_M (act x2) new))) &
                                       (EQ_M (act x1) new) mx2rn1 O))))) O) # (if_then_else_M (EQ_M (to x3) (i 1))
                           (if_then_else_M
                              (((((((EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x3) (i 1))) &
                                   (EQ_M (to x2) (i 2))) &
                                  (EQ_M (to x1) (i 1))) &
                                 (notb (EQ_M (act x3) new))) &
                                (EQ_M (act x1) new)) & 
                               (EQ_M (m x2) grn1)) & 
                              (EQ_M (m x3) grn2) grn21
                              (if_then_else_M
                                 (((((((EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x3) (i 1))) &
                                      (EQ_M (to x2) (i 2))) &
                                     (EQ_M (to x1) (i 1))) &
                                    (notb (EQ_M (act x3) new))) &
                                   (EQ_M (act x1) new)) & 
                                  (EQ_M (m x2) grn1)) & 
                                 (EQ_M (m x3) grn2) grn21
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x1) (i 2)) mx1rn1
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x3) (i 2)) mx3rn3
                                       (if_then_else_M
                                          ((((EQ_M (reveal x4) (i 1)) &
                                             (EQ_M (to x2) (i 1))) &
                                            (EQ_M (to x1) (i 1))) &
                                           (notb (EQ_M (act x2) new))) &
                                          (EQ_M (act x1) new) mx2rn1 O))))) O)).


assert(e_then_2_1:  (if_then_else_M
                              (((((((EQ_M (reveal x4) (i 1)) &
                                    (EQ_M (to x3) (i 1))) &
                                   (EQ_M (to x2) (i 2))) &
                                  (EQ_M (to x1) (i 1))) &
                                 (notb (EQ_M (act x3) new))) &
                                (EQ_M (act x1) new)) & 
                               (EQ_M (m x2) grn1)) & 
                              (EQ_M (m x3) grn2) mx3rn1
                              (if_then_else_M
                                 (EQ_M (reveal x4) (i 2)) &
                                 (EQ_M (to x1) (i 2)) mx1rn1
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x3) (i 2)) mx3rn3
                                    (if_then_else_M
                                       ((((EQ_M (reveal x4) (i 1)) &
                                          (EQ_M (to x2) (i 1))) &
                                         (EQ_M (to x1) (i 1))) &
                                        (notb (EQ_M (act x2) new))) &
                                       (EQ_M (act x1) new) mx2rn1 O)))) #  (if_then_else_M
              (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                   (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                 (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
               (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                 mx1rn1
                 (if_then_else_M
                    (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn3
                    (if_then_else_M
                       ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                         (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                       (EQ_M (act x1) new) mx2rn1 O))))).


pose proof(andB_comm 0 1).

apply Forall_ELM_EVAL_B with (n:= 0) (b:= (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1))) in H.
apply Forall_ELM_EVAL_B with (n:= 1) (b:= (EQ_M (m x3) grn2)) in H. simpl in H.

rewrite H. clear H.

pose proof(IFMORPH_M2 0  (if_then_else_B
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 1)) FAlse)
                        (EQ_M (to (f mphi1)) (i 2)) FAlse)
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r 1))) FAlse) FAlse mx3rn1  (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2)) mx1rn1
         (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
            mx3rn3
            (if_then_else_M
               ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                 (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
               (EQ_M (act x1) new) mx2rn1 O))) ).
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x3) grn2) ) in H. simpl in H.
rewrite H.
clear H.

pose proof (EQBRmsg_msg   (if_then_else_M
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 1)) FAlse)
                        (EQ_M (to (f mphi1)) (i 2)) FAlse)
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r  1))) FAlse)
         (exp (pi1 (ggen (N 0))) (Mvar 2) (r 1))
         (if_then_else_M
            (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
               (EQ_M (to (f mphi0)) (i 2)) FAlse)
            (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r  1))
            (if_then_else_M
               (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                  (EQ_M (to (f mphi2)) (i 2)) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r 3))
               (if_then_else_M
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi1)) (i 1)) FAlse)
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r  1)) O))))  (if_then_else_M FAlse (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r  1))
         (if_then_else_M
            (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
               (EQ_M (to (f mphi0)) (i 2)) FAlse)
            (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r 1))
            (if_then_else_M
               (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                  (EQ_M (to (f mphi2)) (i 2)) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r 3))
               (if_then_else_M
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi1)) (i 1)) FAlse)
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r  1)) O)))) 0 1 2).

pose proof(Forall_ELM_EVAL_M1).
apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x3) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn2 ) in H. simpl in H.
rewrite  H. clear H.
redg.



pose proof(IFMORPH_M2 0  (if_then_else_B
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 1)) FAlse)
                        (EQ_M (to (f mphi1)) (i 2)) FAlse)
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r  1))) FAlse) FAlse grn21  (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
           mx1rn1
           (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))
              mx3rn3
              (if_then_else_M
                 ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                   (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                 (EQ_M (act x1) new) mx2rn1 O))) ).
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x3) grn2) ) in H. simpl in H.
rewrite H. clear H0 H. repeat redg. reflexivity.
rewrite e_then_2_1.



pose proof(andB_assoc 0 1 2) .

pose proof(andB_comm 0 1).
apply Forall_ELM_EVAL_B with (n:= 1) (b:= ((Bvar 1) & (Bvar 2))) in H0. simpl in H0.
rewrite H0 in H; clear H0.
pose proof(andB_assoc 1 2 0).

rewrite <-H0 in H. clear H0.
apply Forall_ELM_EVAL_B with (n:= 1) (b:=  (EQ_M (m x2) grn1)) in H.
apply Forall_ELM_EVAL_B with (n:= 0) (b:= ((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) in H. 
apply Forall_ELM_EVAL_B with (n:= 2) (b:= (EQ_M (m x3) grn2)) in H.
 simpl in H.
rewrite <- H.
clear H.



pose proof(IFMORPH_M2 0  (if_then_else_B (EQ_M (m x3) grn2)
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 1)) FAlse)
                           (EQ_M (to (f mphi1)) (i 2)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
         mx2rn2
         (if_then_else_M
            (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
            (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
               mx1rn1
               (if_then_else_M
                  (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn3
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1 O)))) ) . 
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x2) grn1) ) in H. simpl in H.
rewrite H.
clear H.

repeat redg.  

pose proof (EQBRmsg_msg (if_then_else_M
            (if_then_else_B
               (EQ_M (m (f mphi2))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (EQ_M (to (f mphi2)) (i 1)) FAlse)
                           (EQ_M (to (f mphi1)) (i 2)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse)
            (exp (pi1 (ggen (N 0))) (Mvar 2) (rr (N 2)))
            (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi2)) (i 1)) FAlse)
                                 (EQ_M (to (f mphi1)) (i 2)) FAlse)
                              (EQ_M (to (f mphi0)) (i 1)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (EQ_M (m (f mphi1))
                        (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                     FAlse)
                  (EQ_M (m (f mphi2))
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
                  FAlse)
               (exp (pi1 (ggen (N 0)))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))
                  (rr (N 1)))
               (if_then_else_M
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                     (EQ_M (to (f mphi0)) (i 2)) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 1)))
                  (if_then_else_M
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                        (EQ_M (to (f mphi2)) (i 2)) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 3)))
                     (if_then_else_M
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                 (EQ_M (to (f mphi0)) (i 1)) FAlse)
                              (if_then_else_B (EQ_M (act (f mphi1)) new)
                                 FAlse TRue) FAlse)
                           (EQ_M (act (f mphi0)) new) FAlse)
                        (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O)))))
         (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                 (EQ_M (to (f mphi2)) (i 1)) FAlse)
                              (EQ_M (to (f mphi1)) (i 2)) FAlse)
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (EQ_M (m (f mphi1))
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                  FAlse)
               (EQ_M (m (f mphi2))
                  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
               FAlse)
            (exp (pi1 (ggen (N 0)))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))
               (rr (N 1)))
            (if_then_else_M
               (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                  (EQ_M (to (f mphi0)) (i 2)) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 1)))
               (if_then_else_M
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                     (EQ_M (to (f mphi2)) (i 2)) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 3)))
                  (if_then_else_M
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                 (EQ_M (to (f mphi1)) (i 1)) FAlse)
                              (EQ_M (to (f mphi0)) (i 1)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O))))
      0 1 2).


apply Forall_ELM_EVAL_M1 with (n:= 0) (x:= (m x2) ) in H. simpl in H.

apply Forall_ELM_EVAL_M1 with (n:= 1) (x:= grn1 ) in H. simpl in H.
rewrite  H. clear H.



pose proof(IFMORPH_M2 0   (if_then_else_B (EQ_M (m x3) grn2)
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B
                             (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                                (EQ_M (to (f mphi2)) (i 1)) FAlse)
                             (EQ_M (to (f mphi1)) (i 2)) FAlse)
                          (EQ_M (to (f mphi0)) (i 1)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse) FAlse) FAlse
           grn21
           (if_then_else_M
              (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                   (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                 (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
               (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2) grn21
              (if_then_else_M (EQ_M (reveal x4) (i 2)) & (EQ_M (to x1) (i 2))
                 mx1rn1
                 (if_then_else_M
                    (EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2)) mx3rn3
                    (if_then_else_M
                       ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                         (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                       (EQ_M (act x1) new) mx2rn1 O))))) .
apply Forall_ELM_EVAL_M with (n:= 0) (x:=(EQ_M (m x2) grn1) ) in H.
simpl in H. red_in H.
rewrite H.   rewrite commexp.
reflexivity.  rewrite e_then_2. reflexivity.  rewrite thn. rewrite e_then. reflexivity. Qed.
