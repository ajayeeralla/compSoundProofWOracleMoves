pose proof(IFMORPH_B4 0   FAlse    (EQ_M 
                                                  (m (f mphi2))
                                                  (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (pi2 (ggen (N 0)))
                                                  (r (N 2)))) FAlse );
apply Forall_ELM_EVAL_B with (n:=0) (b:=(EQ_M (act (f mphi2)) new)) in H;
simpl in H;

apply Forall_ELM_EVAL_B with (n:=1) (b:=   (EQ_M 
                                                  (m (f mphi1))
                                                  (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (pi2 (ggen (N 0)))
                                                  (r (N 1))))) in H;
simpl in H; try rewrite IFSAME_B in H;
rewrite H;
clear H.



(****************************************************)

pose proof(IFEVAL_M 1 (exp (pi1 (ggen (N 0))) 
                                       (m (f mphi1)) 
                                       (r (N 2)))
                                    (if_then_else_M
                                       (if_then_else_B
                                          (EQ_M (reveal (f mphi3)) (i 1))
                                          (if_then_else_B
                                            (Bvar 1)
                                             (if_then_else_B
                                                (EQ_M (act (f mphi2)) new)
                                                FAlse
                                                (if_then_else_B
                                                  (EQ_M 
                                                  (m (f mphi1))
                                                  (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (pi2 (ggen (N 0)))
                                                  (r (N 1))))
                                                  (EQ_M 
                                                  (m (f mphi2))
                                                  (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (pi2 (ggen (N 0)))
                                                  (r (N 2)))) FAlse)) FAlse)
                                          FAlse)
                                       (exp (pi1 (ggen (N 0))) 
                                          (m (f mphi2)) 
                                          (r (N 1)))
                                       (if_then_else_M
                                          (EQ_M (to (f mphi0)) (i 2))
                                          (exp (pi1 (ggen (N 0)))
                                             (m (f mphi0)) 
                                             (r (N 1)))
                                          (exp (pi1 (ggen (N 0)))
                                             (m (f mphi2)) 
                                             (r (N 3)))))).


simpl in H;

repeat (try rewrite IFTRUE_M in H; try rewrite IFFALSE_M in H; try rewrite IFSAME_M in H;try rewrite IFTRUE_B in H; try rewrite IFFALSE_B in H; try rewrite IFSAME_B in H);

apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to (f mphi2)) (i 1)) ) in H;

apply Forall_ELM_EVAL_M with (n:=2) (x:= (if_then_else_B
                                       (EQ_M (to (f mphi1)) (i 2))
                                       (if_then_else_B
                                          (EQ_M (act (f mphi2)) new) FAlse
                                          (if_then_else_B
                                             (EQ_M 
                                                (m (f mphi1))
                                                (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (pi2 (ggen (N 0)))
                                                  (r (N 1))))
                                             (EQ_M 
                                                (m (f mphi2))
                                                (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (pi2 (ggen (N 0)))
                                                  (r (N 2)))) FAlse)) FAlse)) in H;
simpl in H;
rewrite H;
clear H.






pose proof(IFMORPH_M2 0   (if_then_else_B (EQ_M (to (f mphi2)) (i 1))
                                 (if_then_else_B (EQ_M (to (f mphi1)) (i 2))
                                    (if_then_else_B
                                       (EQ_M (act (f mphi2)) new) FAlse
                                       (if_then_else_B
                                          (EQ_M (m (f mphi1))
                                             (exp (pi1 (ggen (N 0)))
                                                (pi2 (ggen (N 0))) 
                                                (r (N 1))))
                                          (EQ_M (m (f mphi2))
                                             (exp (pi1 (ggen (N 0)))
                                                (pi2 (ggen (N 0))) 
                                                (r (N 2)))) FAlse)) FAlse)
                                 FAlse) FAlse  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 2))) );
            apply Forall_ELM_EVAL_M with (n:=0) (x:=    (EQ_M (act (f mphi1)) new)) in H;
simpl in H;  try rewrite IFFALSE_M in H; rewrite H; clear H.



pose proof(IFTF 3);apply Forall_ELM_EVAL_B with (n:=3) (b:=  (EQ_M (to (f mphi1)) (i 2))) in H;simpl in H; rewrite H ; clear H.


pose proof(IFMORPH_B1     FAlse
                                          (EQ_M (to (f mphi1)) (i 2)) FAlse 0 1 );
rewrite IFSAME_B in H;

apply Forall_ELM_EVAL_B with (n:=1) (b:=(EQ_M (to (f mphi2)) (i 1))) in H;
simpl in H;

apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (act (f mphi2)) new)) in H;
simpl in H;
rewrite H;
clear  H. 





 pose proof(IFMORPH_B4 0   FAlse  (EQ_M (to (f mphi1)) (i 2)) FAlse );
apply Forall_ELM_EVAL_B with (n:=0) (b:= (EQ_M (act (f mphi2)) new) ) in H;
simpl in H;

apply Forall_ELM_EVAL_B with (n:=1) (b:= (EQ_M (to (f mphi2)) (i 1))) in H;
simpl in H; try rewrite IFSAME_B in H;
rewrite H;
clear H.



  pose proof(IFMORPH_B1    FAlse  (EQ_M (to (f mphi1)) (i 2)) FAlse  0 1);
rewrite IFSAME_B in H;

apply Forall_ELM_EVAL_B with (n:=1) (b:= (EQ_M (to (f mphi2)) (i 1))) in H;
simpl in H;

apply Forall_ELM_EVAL_B with (n:=0) (b:=   (EQ_M (act (f mphi2)) new)) in H;
simpl in H;
rewrite H;
clear H. 


pose proof(IFMORPH_B4 0   FAlse  (EQ_M (to (f mphi1)) (i 2)) FAlse );
apply Forall_ELM_EVAL_B with (n:=0) (b:= (EQ_M (act (f mphi2)) new) ) in H;
simpl in H;

apply Forall_ELM_EVAL_B with (n:=1) (b:= (EQ_M (to (f mphi2)) (i 1))) in H;
simpl in H; try rewrite IFSAME_B in H;
rewrite H;
clear H.


pose proof(IFMORPH_B1    (if_then_else_B
                                          (EQ_M (act (f mphi2)) new) FAlse
                                          (EQ_M (to (f mphi1)) (i 2))) FAlse
                                    FAlse  0 1);
rewrite IFSAME_B in H;

apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (to (f mphi2)) (i 1))) in H;
simpl in H;

apply Forall_ELM_EVAL_B with (n:=1) (b:=    (EQ_M (reveal (f mphi3)) (i 2))) in H;
simpl in H;
rewrite H;
clear H. 
pose proof(IFMORPH_B1    FAlse
                                          (EQ_M (to (f mphi1)) (i 2)) FAlse  0 1);
rewrite IFSAME_B in H;

apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (act (f mphi2)) new)) in H;
simpl in H;

apply Forall_ELM_EVAL_B with (n:=1) (b:=   (EQ_M (reveal (f mphi3)) (i 2))) in H;
simpl in H;
rewrite H;
clear H. 

pose proof(IFMORPH_B4 0   FAlse  (EQ_M (to (f mphi1)) (i 2)) FAlse );
apply Forall_ELM_EVAL_B with (n:=0) (b:= (EQ_M (act (f mphi2)) new) ) in H;
simpl in H;

apply Forall_ELM_EVAL_B with (n:=1) (b:=  (EQ_M (reveal (f mphi3)) (i 2))) in H;
simpl in H; try rewrite IFSAME_B in H;
rewrite H;
clear H.

pose proof(IFMORPH_B2 0  (EQ_M (to (f mphi1)) (i 2)) FAlse
                                       (if_then_else_B
                                          (EQ_M (act (f mphi2)) new) FAlse
                                          TRue) FAlse);
simpl in H ;rewrite IFFALSE_B in H;
apply Forall_ELM_EVAL_B with (n:=0) (b:=    (EQ_M (to (f mphi2)) (i 1))) in H;
simpl in H;
rewrite H; clear H.




assert(TFm2m2' : ( [msg ( (0 := TRue) ((1 := FAlse)   (if_then_else_M(Bvar 0)
      (if_then_else_M (EQ_M (reveal x2) (i 2)) O
         (if_then_else_M (EQ_M (reveal x2) (i 1)) &(Bvar 0)
            (if_then_else_M (EQ_M (reveal x3) (i 2)) O
               (if_then_else_M (EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)
                  (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                     (if_then_else_M (EQ_M (to x2) (i 2)) acc O)) O))
            (if_then_else_M (EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)
               (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                  (if_then_else_M
                     (EQ_M (reveal x3) (i 1)) &(Bvar 0)
                     (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                        (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                     (if_then_else_M
                        (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))
                        (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                           (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                        (if_then_else_M (EQ_M (to x3) (i 2))
                           (if_then_else_M
                              (EQ_M (reveal x4) (i 1)) &(Bvar 0)
                              mx1rn1
                              (if_then_else_M
                                 (EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x2) (i 1)) mx2rn2
                                 (if_then_else_M
                                    ((((EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x2) (i 2))) &
                                      (EQ_M (to x1) (i 2))) &
                                     (notb (EQ_M (act x2) new))) &
                                    (Bvar 1) mx2rn1
                                    (if_then_else_M
                                       ((((EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x3) (i 2))) &
                                         (EQ_M (to x2) (i 2))) &
                                        (notb (EQ_M (act x3) new))) &
                                       (EQ_M (act x2) new) mx3rn2 O)))) O))))
               O)))
      (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 1)
         (if_then_else_M (EQ_M (reveal x2) (i 1)) O
            (if_then_else_M (EQ_M (reveal x2) (i 2)) O
               (if_then_else_M (EQ_M (to x2) (i 2))
                  (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                     (if_then_else_M
                        ((((EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2))) &
                          (EQ_M (to x1) (i 2))) & (notb (EQ_M (act x2) new))) &
                        (Bvar 1)
                        (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                           (if_then_else_M (EQ_M (to x4) (i 1)) grn4 O))
                        (if_then_else_M (EQ_M (to x3) (i 1))
                           (if_then_else_M
                              (EQ_M (reveal x4) (i 1)) &(Bvar 0)
                              mx1rn1
                              (if_then_else_M
                                 (EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x2) (i 1)) mx2rn2
                                 (if_then_else_M
                                    ((((EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x2) (i 2))) &
                                      (EQ_M (to x1) (i 2))) &
                                     (notb (EQ_M (act x2) new))) &
                                    (Bvar 1) mx2rn1
                                    (if_then_else_M
                                       ((((EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x3) (i 2))) &
                                         (EQ_M (to x2) (i 2))) &
                                        (notb (EQ_M (act x3) new))) &
                                       (EQ_M (act x2) new) mx3rn2 O)))) O)))
                  (if_then_else_M (EQ_M (to x2) (i 1))
                     (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                        (if_then_else_M
                           (EQ_M (reveal x3) (i 1)) &(Bvar 0)
                           (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                              (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                           (if_then_else_M
                              (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))
                              (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                                 (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                              (if_then_else_M (EQ_M (to x3) (i 2))
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 1)) &
                                   (Bvar 0) mx1rn1
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x2) (i 1)) mx2rn2
                                       (if_then_else_M
                                          ((((EQ_M (reveal x4) (i 2)) &
                                             (EQ_M (to x2) (i 2))) &
                                            (EQ_M (to x1) (i 2))) &
                                           (notb (EQ_M (act x2) new))) &
                                          (Bvar 1) mx2rn1
                                          (if_then_else_M
                                             ((((EQ_M (reveal x4) (i 2)) &
                                                (EQ_M (to x3) (i 2))) &
                                               (EQ_M (to x2) (i 2))) &
                                              (notb (EQ_M (act x3) new))) &
                                             (EQ_M (act x2) new) mx3rn2 O))))
                                 O)))) O))))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (reveal x2) (i 1)) O
               (if_then_else_M
                  (EQ_M (reveal x2) (i 1)) &(Bvar 0)
                  (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                     (if_then_else_M
                        (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                        (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                           (if_then_else_M (EQ_M (to x4) (i 1)) acc O)) O))
                  (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                     (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                        (if_then_else_M
                           (EQ_M (reveal x3) (i 2)) & (EQ_M (to x1) (i 2))
                           (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                              (if_then_else_M (EQ_M (to x4) (i 1)) acc O))
                           (if_then_else_M (EQ_M (to x3) (i 1))
                              (if_then_else_M
                                 (EQ_M (reveal x4) (i 2)) &
                                 (EQ_M (to x1) (i 2)) mx1rn1
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x3) (i 2)) mx3rn3
                                    (if_then_else_M
                                       ((((EQ_M (reveal x4) (i 1)) &
                                          (EQ_M (to x2) (i 1))) &
                                        (Bvar 0)) &
                                        (notb (EQ_M (act x2) new))) &
                                       (Bvar 1) mx2rn1 O))) O))) O)))
            O))) )  )]) ~ [msg ((0 := TRue) ((1 := FAlse) (if_then_else_M(Bvar 0)
        (if_then_else_M (EQ_M (reveal x2) (i 2)) O
           (if_then_else_M (EQ_M (reveal x2) (i 1)) &(Bvar 0)
              (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                 (if_then_else_M (EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)
                    (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                       (if_then_else_M (EQ_M (to x2) (i 2)) acc O)) O))
              (if_then_else_M (EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)
                 (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                    (if_then_else_M
                       (EQ_M (reveal x3) (i 1)) &(Bvar 0)
                       (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                          (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                       (if_then_else_M
                          (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))
                          (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                             (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                          (if_then_else_M (EQ_M (to x3) (i 2))
                             (if_then_else_M
                                (((((((EQ_M (reveal x4) (i 1)) &
                                      (EQ_M (to x3) (i 2))) &
                                     (EQ_M (to x2) (i 1))) &
                                    (EQ_M (to x1) (i 2))) &
                                   (notb (EQ_M (act x3) new))) &
                                  (Bvar 1)) & 
                                 (EQ_M (m x2) grn1)) & 
                                (EQ_M (m x3) grn2) mx2rn2
                                (if_then_else_M
                                   (((((((EQ_M (reveal x4) (i 2)) &
                                         (EQ_M (to x3) (i 2))) &
                                        (EQ_M (to x2) (i 1))) &
                                       (EQ_M (to x1) (i 2))) &
                                      (notb (EQ_M (act x3) new))) &
                                     (Bvar 1)) &
                                    (EQ_M (m x2) grn1)) & 
                                   (EQ_M (m x3) grn2) mx3rn1
                                   (if_then_else_M
                                      (EQ_M (reveal x4) (i 1)) &
                                     (Bvar 0) mx1rn1
                                      (if_then_else_M
                                         (EQ_M (reveal x4) (i 1)) &
                                         (EQ_M (to x2) (i 1)) mx2rn2
                                         (if_then_else_M
                                            ((((EQ_M (reveal x4) (i 2)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 2))) &
                                             (notb (EQ_M (act x2) new))) &
                                            (Bvar 1) mx2rn1
                                            (if_then_else_M
                                               ((((EQ_M (reveal x4) (i 2)) &
                                                  (EQ_M (to x3) (i 2))) &
                                                 (EQ_M (to x2) (i 2))) &
                                                (notb (EQ_M (act x3) new))) &
                                               (EQ_M (act x2) new) mx3rn2 O))))))
                             O)))) O)))
        (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 1)
           (if_then_else_M (EQ_M (reveal x2) (i 1)) O
              (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                 (if_then_else_M (EQ_M (to x2) (i 2))
                    (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                       (if_then_else_M
                          ((((EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2))) &
                            (EQ_M (to x1) (i 2))) &
                           (notb (EQ_M (act x2) new))) & 
                          (Bvar 1)
                          (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                             (if_then_else_M (EQ_M (to x4) (i 1)) grn4 O))
                          (if_then_else_M (EQ_M (to x3) (i 1))
                             (if_then_else_M
                                (((((((EQ_M (reveal x4) (i 1)) &
                                      (EQ_M (to x3) (i 2))) &
                                     (EQ_M (to x2) (i 1))) &
                                    (EQ_M (to x1) (i 2))) &
                                   (notb (EQ_M (act x3) new))) &
                                  (Bvar 1)) & 
                                 (EQ_M (m x2) grn1)) & 
                                (EQ_M (m x3) grn2) mx2rn2
                                (if_then_else_M
                                   (((((((EQ_M (reveal x4) (i 2)) &
                                         (EQ_M (to x3) (i 2))) &
                                        (EQ_M (to x2) (i 1))) &
                                       (EQ_M (to x1) (i 2))) &
                                      (notb (EQ_M (act x3) new))) &
                                     (Bvar 1)) &
                                    (EQ_M (m x2) grn1)) & 
                                   (EQ_M (m x3) grn2) mx3rn1
                                   (if_then_else_M
                                      (EQ_M (reveal x4) (i 1)) &
                                     (Bvar 0) mx1rn1
                                      (if_then_else_M
                                         (EQ_M (reveal x4) (i 1)) &
                                         (EQ_M (to x2) (i 1)) mx2rn2
                                         (if_then_else_M
                                            ((((EQ_M (reveal x4) (i 2)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 2))) &
                                             (notb (EQ_M (act x2) new))) &
                                            (Bvar 1) mx2rn1
                                            (if_then_else_M
                                               ((((EQ_M (reveal x4) (i 2)) &
                                                  (EQ_M (to x3) (i 2))) &
                                                 (EQ_M (to x2) (i 2))) &
                                                (notb (EQ_M (act x3) new))) &
                                               (EQ_M (act x2) new) mx3rn2 O))))))
                             O)))
                    (if_then_else_M (EQ_M (to x2) (i 1))
                       (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                          (if_then_else_M
                             (EQ_M (reveal x3) (i 1)) &(Bvar 0)
                             (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                                (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                             (if_then_else_M
                                (EQ_M (reveal x3) (i 1)) &
                                (EQ_M (to x2) (i 1))
                                (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                                   (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                                (if_then_else_M (EQ_M (to x3) (i 2))
                                   (if_then_else_M
                                      (((((((EQ_M (reveal x4) (i 1)) &
                                            (EQ_M (to x3) (i 2))) &
                                           (EQ_M (to x2) (i 1))) &
                                          (EQ_M (to x1) (i 2))) &
                                         (notb (EQ_M (act x3) new))) &
                                        (Bvar 1)) &
                                       (EQ_M (m x2) grn1)) &
                                      (EQ_M (m x3) grn2) mx2rn2
                                      (if_then_else_M
                                         (((((((EQ_M (reveal x4) (i 2)) &
                                               (EQ_M (to x3) (i 2))) &
                                              (EQ_M (to x2) (i 1))) &
                                             (EQ_M (to x1) (i 2))) &
                                            (notb (EQ_M (act x3) new))) &
                                           (Bvar 1)) &
                                          (EQ_M (m x2) grn1)) &
                                         (EQ_M (m x3) grn2) mx3rn1
                                         (if_then_else_M
                                            (EQ_M (reveal x4) (i 1)) &
                                           (Bvar 0) mx1rn1
                                            (if_then_else_M
                                               (EQ_M (reveal x4) (i 1)) &
                                               (EQ_M (to x2) (i 1)) mx2rn2
                                               (if_then_else_M
                                                  ((((EQ_M (reveal x4) (i 2)) &
                                                  (EQ_M (to x2) (i 2))) &
                                                  (EQ_M (to x1) (i 2))) &
                                                  (notb (EQ_M (act x2) new))) &
                                                  (Bvar 1) mx2rn1
                                                  (if_then_else_M
                                                  ((((EQ_M (reveal x4) (i 2)) &
                                                  (EQ_M (to x3) (i 2))) &
                                                  (EQ_M (to x2) (i 2))) &
                                                  (notb (EQ_M (act x3) new))) &
                                                  (EQ_M (act x2) new) mx3rn2
                                                  O)))))) O)))) O))))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                 (if_then_else_M
                    (EQ_M (reveal x2) (i 1)) &(Bvar 0)
                    (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                       (if_then_else_M
                          (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                          (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                             (if_then_else_M (EQ_M (to x4) (i 1)) acc O)) O))
                    (if_then_else_M
                       (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                       (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                          (if_then_else_M
                             (EQ_M (reveal x3) (i 2)) & (EQ_M (to x1) (i 2))
                             (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                                (if_then_else_M (EQ_M (to x4) (i 1)) acc O))
                             (if_then_else_M (EQ_M (to x3) (i 1))
                                (if_then_else_M
                                   (((((((EQ_M (reveal x4) (i 2)) &
                                         (EQ_M (to x3) (i 1))) &
                                        (EQ_M (to x2) (i 2))) &
                                      (Bvar 0)) &
                                      (notb (EQ_M (act x3) new))) &
                                     (Bvar 1)) &
                                    (EQ_M (m x2) grn1)) & 
                                   (EQ_M (m x3) grn2) mx2rn2
                                   (if_then_else_M
                                      (((((((EQ_M (reveal x4) (i 1)) &
                                            (EQ_M (to x3) (i 1))) &
                                           (EQ_M (to x2) (i 2))) &
                                         (Bvar 0)) &
                                         (notb (EQ_M (act x3) new))) &
                                        (Bvar 1)) &
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
                                                (Bvar 0)) &
                                                (notb (EQ_M (act x2) new))) &
                                               (Bvar 1) mx2rn1 O)))))
                                O))) O))) O))) )) ]).


simpl.



assert(Fm2m2':  [msg ( (0 := TRue)   (if_then_else_M(Bvar 0)
      (if_then_else_M (EQ_M (reveal x2) (i 2)) O
         (if_then_else_M (EQ_M (reveal x2) (i 1)) &(Bvar 0)
            (if_then_else_M (EQ_M (reveal x3) (i 2)) O
               (if_then_else_M (EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)
                  (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                     (if_then_else_M (EQ_M (to x2) (i 2)) acc O)) O))
            (if_then_else_M (EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)
               (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                  (if_then_else_M
                     (EQ_M (reveal x3) (i 1)) &(Bvar 0)
                     (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                        (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                     (if_then_else_M
                        (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))
                        (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                           (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                        (if_then_else_M (EQ_M (to x3) (i 2))
                           (if_then_else_M
                              (EQ_M (reveal x4) (i 1)) &(Bvar 0)
                              mx1rn1
                              (if_then_else_M
                                 (EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x2) (i 1)) mx2rn2
                                 (if_then_else_M
                                    ((((EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x2) (i 2))) &
                                      (EQ_M (to x1) (i 2))) &
                                     (notb (EQ_M (act x2) new))) &
                                    (Bvar 1) mx2rn1
                                    (if_then_else_M
                                       ((((EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x3) (i 2))) &
                                         (EQ_M (to x2) (i 2))) &
                                        (notb (EQ_M (act x3) new))) &
                                       (EQ_M (act x2) new) mx3rn2 O)))) O))))
               O)))
      (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 1)
         (if_then_else_M (EQ_M (reveal x2) (i 1)) O
            (if_then_else_M (EQ_M (reveal x2) (i 2)) O
               (if_then_else_M (EQ_M (to x2) (i 2))
                  (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                     (if_then_else_M
                        ((((EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2))) &
                          (EQ_M (to x1) (i 2))) & (notb (EQ_M (act x2) new))) &
                        (Bvar 1)
                        (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                           (if_then_else_M (EQ_M (to x4) (i 1)) grn4 O))
                        (if_then_else_M (EQ_M (to x3) (i 1))
                           (if_then_else_M
                              (EQ_M (reveal x4) (i 1)) &(Bvar 0)
                              mx1rn1
                              (if_then_else_M
                                 (EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x2) (i 1)) mx2rn2
                                 (if_then_else_M
                                    ((((EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x2) (i 2))) &
                                      (EQ_M (to x1) (i 2))) &
                                     (notb (EQ_M (act x2) new))) &
                                    (Bvar 1) mx2rn1
                                    (if_then_else_M
                                       ((((EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x3) (i 2))) &
                                         (EQ_M (to x2) (i 2))) &
                                        (notb (EQ_M (act x3) new))) &
                                       (EQ_M (act x2) new) mx3rn2 O)))) O)))
                  (if_then_else_M (EQ_M (to x2) (i 1))
                     (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                        (if_then_else_M
                           (EQ_M (reveal x3) (i 1)) &(Bvar 0)
                           (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                              (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                           (if_then_else_M
                              (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))
                              (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                                 (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                              (if_then_else_M (EQ_M (to x3) (i 2))
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 1)) &
                                   (Bvar 0) mx1rn1
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x2) (i 1)) mx2rn2
                                       (if_then_else_M
                                          ((((EQ_M (reveal x4) (i 2)) &
                                             (EQ_M (to x2) (i 2))) &
                                            (EQ_M (to x1) (i 2))) &
                                           (notb (EQ_M (act x2) new))) &
                                          (Bvar 1) mx2rn1
                                          (if_then_else_M
                                             ((((EQ_M (reveal x4) (i 2)) &
                                                (EQ_M (to x3) (i 2))) &
                                               (EQ_M (to x2) (i 2))) &
                                              (notb (EQ_M (act x3) new))) &
                                             (EQ_M (act x2) new) mx3rn2 O))))
                                 O)))) O))))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (reveal x2) (i 1)) O
               (if_then_else_M
                  (EQ_M (reveal x2) (i 1)) &(Bvar 0)
                  (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                     (if_then_else_M
                        (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                        (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                           (if_then_else_M (EQ_M (to x4) (i 1)) acc O)) O))
                  (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                     (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                        (if_then_else_M
                           (EQ_M (reveal x3) (i 2)) & (EQ_M (to x1) (i 2))
                           (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                              (if_then_else_M (EQ_M (to x4) (i 1)) acc O))
                           (if_then_else_M (EQ_M (to x3) (i 1))
                              (if_then_else_M
                                 (EQ_M (reveal x4) (i 2)) &
                                 (EQ_M (to x1) (i 2)) mx1rn1
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x3) (i 2)) mx3rn3
                                    (if_then_else_M
                                       ((((EQ_M (reveal x4) (i 1)) &
                                          (EQ_M (to x2) (i 1))) &
                                        (Bvar 0)) &
                                        (notb (EQ_M (act x2) new))) &
                                       (Bvar 1) mx2rn1 O))) O))) O)))
            O))) )] ~ [msg ((0 := FAlse)   (if_then_else_M(Bvar 0)
        (if_then_else_M (EQ_M (reveal x2) (i 2)) O
           (if_then_else_M (EQ_M (reveal x2) (i 1)) &(Bvar 0)
              (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                 (if_then_else_M (EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)
                    (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                       (if_then_else_M (EQ_M (to x2) (i 2)) acc O)) O))
              (if_then_else_M (EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)
                 (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                    (if_then_else_M
                       (EQ_M (reveal x3) (i 1)) &(Bvar 0)
                       (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                          (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                       (if_then_else_M
                          (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))
                          (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                             (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                          (if_then_else_M (EQ_M (to x3) (i 2))
                             (if_then_else_M
                                (((((((EQ_M (reveal x4) (i 1)) &
                                      (EQ_M (to x3) (i 2))) &
                                     (EQ_M (to x2) (i 1))) &
                                    (EQ_M (to x1) (i 2))) &
                                   (notb (EQ_M (act x3) new))) &
                                  (Bvar 1)) & 
                                 (EQ_M (m x2) grn1)) & 
                                (EQ_M (m x3) grn2) mx2rn2
                                (if_then_else_M
                                   (((((((EQ_M (reveal x4) (i 2)) &
                                         (EQ_M (to x3) (i 2))) &
                                        (EQ_M (to x2) (i 1))) &
                                       (EQ_M (to x1) (i 2))) &
                                      (notb (EQ_M (act x3) new))) &
                                     (Bvar 1)) &
                                    (EQ_M (m x2) grn1)) & 
                                   (EQ_M (m x3) grn2) mx3rn1
                                   (if_then_else_M
                                      (EQ_M (reveal x4) (i 1)) &
                                     (Bvar 0) mx1rn1
                                      (if_then_else_M
                                         (EQ_M (reveal x4) (i 1)) &
                                         (EQ_M (to x2) (i 1)) mx2rn2
                                         (if_then_else_M
                                            ((((EQ_M (reveal x4) (i 2)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 2))) &
                                             (notb (EQ_M (act x2) new))) &
                                            (Bvar 1) mx2rn1
                                            (if_then_else_M
                                               ((((EQ_M (reveal x4) (i 2)) &
                                                  (EQ_M (to x3) (i 2))) &
                                                 (EQ_M (to x2) (i 2))) &
                                                (notb (EQ_M (act x3) new))) &
                                               (EQ_M (act x2) new) mx3rn2 O))))))
                             O)))) O)))
        (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 1)
           (if_then_else_M (EQ_M (reveal x2) (i 1)) O
              (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                 (if_then_else_M (EQ_M (to x2) (i 2))
                    (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                       (if_then_else_M
                          ((((EQ_M (reveal x3) (i 2)) & (EQ_M (to x2) (i 2))) &
                            (EQ_M (to x1) (i 2))) &
                           (notb (EQ_M (act x2) new))) & 
                          (Bvar 1)
                          (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                             (if_then_else_M (EQ_M (to x4) (i 1)) grn4 O))
                          (if_then_else_M (EQ_M (to x3) (i 1))
                             (if_then_else_M
                                (((((((EQ_M (reveal x4) (i 1)) &
                                      (EQ_M (to x3) (i 2))) &
                                     (EQ_M (to x2) (i 1))) &
                                    (EQ_M (to x1) (i 2))) &
                                   (notb (EQ_M (act x3) new))) &
                                  (Bvar 1)) & 
                                 (EQ_M (m x2) grn1)) & 
                                (EQ_M (m x3) grn2) mx2rn2
                                (if_then_else_M
                                   (((((((EQ_M (reveal x4) (i 2)) &
                                         (EQ_M (to x3) (i 2))) &
                                        (EQ_M (to x2) (i 1))) &
                                       (EQ_M (to x1) (i 2))) &
                                      (notb (EQ_M (act x3) new))) &
                                     (Bvar 1)) &
                                    (EQ_M (m x2) grn1)) & 
                                   (EQ_M (m x3) grn2) mx3rn1
                                   (if_then_else_M
                                      (EQ_M (reveal x4) (i 1)) &
                                     (Bvar 0) mx1rn1
                                      (if_then_else_M
                                         (EQ_M (reveal x4) (i 1)) &
                                         (EQ_M (to x2) (i 1)) mx2rn2
                                         (if_then_else_M
                                            ((((EQ_M (reveal x4) (i 2)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 2))) &
                                             (notb (EQ_M (act x2) new))) &
                                            (Bvar 1) mx2rn1
                                            (if_then_else_M
                                               ((((EQ_M (reveal x4) (i 2)) &
                                                  (EQ_M (to x3) (i 2))) &
                                                 (EQ_M (to x2) (i 2))) &
                                                (notb (EQ_M (act x3) new))) &
                                               (EQ_M (act x2) new) mx3rn2 O))))))
                             O)))
                    (if_then_else_M (EQ_M (to x2) (i 1))
                       (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                          (if_then_else_M
                             (EQ_M (reveal x3) (i 1)) &(Bvar 0)
                             (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                                (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                             (if_then_else_M
                                (EQ_M (reveal x3) (i 1)) &
                                (EQ_M (to x2) (i 1))
                                (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                                   (if_then_else_M (EQ_M (to x2) (i 2)) acc O))
                                (if_then_else_M (EQ_M (to x3) (i 2))
                                   (if_then_else_M
                                      (((((((EQ_M (reveal x4) (i 1)) &
                                            (EQ_M (to x3) (i 2))) &
                                           (EQ_M (to x2) (i 1))) &
                                          (EQ_M (to x1) (i 2))) &
                                         (notb (EQ_M (act x3) new))) &
                                        (Bvar 1)) &
                                       (EQ_M (m x2) grn1)) &
                                      (EQ_M (m x3) grn2) mx2rn2
                                      (if_then_else_M
                                         (((((((EQ_M (reveal x4) (i 2)) &
                                               (EQ_M (to x3) (i 2))) &
                                              (EQ_M (to x2) (i 1))) &
                                             (EQ_M (to x1) (i 2))) &
                                            (notb (EQ_M (act x3) new))) &
                                           (Bvar 1)) &
                                          (EQ_M (m x2) grn1)) &
                                         (EQ_M (m x3) grn2) mx3rn1
                                         (if_then_else_M
                                            (EQ_M (reveal x4) (i 1)) &
                                           (Bvar 0) mx1rn1
                                            (if_then_else_M
                                               (EQ_M (reveal x4) (i 1)) &
                                               (EQ_M (to x2) (i 1)) mx2rn2
                                               (if_then_else_M
                                                  ((((EQ_M (reveal x4) (i 2)) &
                                                  (EQ_M (to x2) (i 2))) &
                                                  (EQ_M (to x1) (i 2))) &
                                                  (notb (EQ_M (act x2) new))) &
                                                  (Bvar 1) mx2rn1
                                                  (if_then_else_M
                                                  ((((EQ_M (reveal x4) (i 2)) &
                                                  (EQ_M (to x3) (i 2))) &
                                                  (EQ_M (to x2) (i 2))) &
                                                  (notb (EQ_M (act x3) new))) &
                                                  (EQ_M (act x2) new) mx3rn2
                                                  O)))))) O)))) O))))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                 (if_then_else_M
                    (EQ_M (reveal x2) (i 1)) &(Bvar 0)
                    (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                       (if_then_else_M
                          (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                          (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                             (if_then_else_M (EQ_M (to x4) (i 1)) acc O)) O))
                    (if_then_else_M
                       (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                       (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                          (if_then_else_M
                             (EQ_M (reveal x3) (i 2)) & (EQ_M (to x1) (i 2))
                             (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                                (if_then_else_M (EQ_M (to x4) (i 1)) acc O))
                             (if_then_else_M (EQ_M (to x3) (i 1))
                                (if_then_else_M
                                   (((((((EQ_M (reveal x4) (i 2)) &
                                         (EQ_M (to x3) (i 1))) &
                                        (EQ_M (to x2) (i 2))) &
                                      (Bvar 0)) &
                                      (notb (EQ_M (act x3) new))) &
                                     (Bvar 1)) &
                                    (EQ_M (m x2) grn1)) & 
                                   (EQ_M (m x3) grn2) mx2rn2
                                   (if_then_else_M
                                      (((((((EQ_M (reveal x4) (i 1)) &
                                            (EQ_M (to x3) (i 1))) &
                                           (EQ_M (to x2) (i 2))) &
                                         (Bvar 0)) &
                                         (notb (EQ_M (act x3) new))) &
                                        (Bvar 1)) &
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
                                                (Bvar 0)) &
                                                (notb (EQ_M (act x2) new))) &
                                               (Bvar 1) mx2rn1 O)))))
                                O))) O))) O))))]).


pose proof(brind_tmind 1 2  qa1000_ss  (if_then_else_M (EQ_M (to x1) (i 1)) qa0010_ss
                  (if_then_else_M (EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)
                     qa0100_ss
                     (if_then_else_M (EQ_M (to x1) (i 2)) qa0001_ss O)))  qc1000_ss  (if_then_else_M (EQ_M (to x1) (i 1)) qc0010_ss
                 (if_then_else_M (EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)
                    qc0100_ss
                    (if_then_else_M (EQ_M (to x1) (i 2)) qc0001_ss O))) ).
simpl in H.
pose proof(mor_eval_andB).
pose proof(mor_eval_andB 1  qa1000_ss  ).
pose proof(brind_tmind 0 1  qa1000_ss  qa0010_ss  (if_then_else_M (EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)
                     qa0100_ss
                     (if_then_else_M (EQ_M (to x1) (i 2)) qa0001_ss O))


(************************************ (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)**********************)

     pose proof (mor_eval_andB 1           (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                  (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                     (if_then_else_M (EQ_M (to x2) (i 1))
                        (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                           (if_then_else_M
                              ((((EQ_M (reveal x3) (i 1)) &
                                 (EQ_M (to x2) (i 1))) & 
                                (Bvar 1)) &
                               (notb (EQ_M (act x2) new))) &
                              (EQ_M (act x1) new) qa3000
                              (if_then_else_M (EQ_M (to x3) (i 2)) qa2001 O)))
                        (if_then_else_M (EQ_M (to x2) (i 2))
                           (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                              (if_then_else_M
                                 (EQ_M (reveal x3) (i 2)) &
                                 (EQ_M (to x1) (i 2)) qa1002
                                 (if_then_else_M (EQ_M (to x3) (i 1)) qa2001
                                    O))) O))))


 (if_then_else_M (Bvar 1)
                  (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                     (if_then_else_M
                        (EQ_M (reveal x2) (i 1)) & (Bvar 1)
                        (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                           (if_then_else_M
                              (EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)
                              qa0120 O))
                        (if_then_else_M
                           (EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)
                           (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                              (if_then_else_M
                                 (EQ_M (reveal x3) (i 1)) &
                                 (Bvar 1) qa0120
                                 (if_then_else_M
                                    (EQ_M (reveal x3) (i 1)) &
                                    (EQ_M (to x2) (i 1)) qa0120
                                    (if_then_else_M 
                                       (EQ_M (to x3) (i 2)) qa0210 O)))) O)))
                  (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 2)
                     (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                        (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                           (if_then_else_M (EQ_M (to x2) (i 2))
                              (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                 (if_then_else_M
                                    ((((EQ_M (reveal x3) (i 2)) &
                                       (EQ_M (to x2) (i 2))) &
                                      (EQ_M (to x1) (i 2))) &
                                     (notb (EQ_M (act x2) new))) &
                                    (Bvar 2) qa0300
                                    (if_then_else_M 
                                       (EQ_M (to x3) (i 1)) qa0210 O)))
                              (if_then_else_M (EQ_M (to x2) (i 1))
                                 (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                                    (if_then_else_M
                                       (EQ_M (reveal x3) (i 1)) &
                                       (Bvar 1) qa0120
                                       (if_then_else_M
                                          (EQ_M (reveal x3) (i 1)) &
                                          (EQ_M (to x2) (i 1)) qa0120
                                          (if_then_else_M
                                             (EQ_M (to x3) (i 2)) qa0210 O))))
                                 O))))
                     (if_then_else_M (EQ_M (to x1) (i 2))
                        (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                           (if_then_else_M
                              (EQ_M (reveal x2) (i 1)) & (Bvar 1)
                              (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                 (if_then_else_M
                                    (EQ_M (to x3) (i 1)) &
                                    (EQ_M (act x3) new) qa1002 O))
                              (if_then_else_M
                                 (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                 (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                    (if_then_else_M
                                       (EQ_M (reveal x3) (i 2)) &
                                       (EQ_M (to x1) (i 2)) qa1002
                                       (if_then_else_M 
                                          (EQ_M (to x3) (i 1)) qa2001 O))) O)))
                        O)))).
simpl in H.


repeat (try rewrite IFTRUE_M in H; try rewrite IFFALSE_M in H; try rewrite IFSAME_M in H;try rewrite IFTRUE_B in H; try rewrite IFFALSE_B in H; try rewrite IFSAME_B in H).

pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (if_then_else_B
                                         (EQ_M (reveal (f mphi2)) (i 1))
                                         (EQ_M (to (f mphi1)) (i 1)) FAlse)) in H0. simpl in H0. 

rewrite H0 in H; clear H0.
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (EQ_M (reveal (f mphi1)) (i 1))) in H0. simpl in H0. 

rewrite H0 in H; clear H0.


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (EQ_M (reveal (f mphi2)) (i 1))) in H0. simpl in H0. 

rewrite H0 in H; clear H0.






apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x1) (i 1))) in H.
 simpl in H.

apply Forall_ELM_EVAL_M with (n:=2) (x:=   (EQ_M (act x1) new)) in H.
 simpl in H.
(****************************************************************************************)


(****************H0 is from Pi2''*******************************)

(*****(EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)*********)

pose proof (mor_eval_andB 1  (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                 (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                    (if_then_else_M (EQ_M (to x2) (i 1))
                       (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                          (if_then_else_M
                             ((((EQ_M (reveal x3) (i 1)) &
                                (EQ_M (to x2) (i 1))) & 
                               (Bvar 1)) &
                              (notb (EQ_M (act x2) new))) &
                             (Bvar 2) qa3000
                             (if_then_else_M (EQ_M (to x3) (i 2)) qc2001 O)))
                       (if_then_else_M (EQ_M (to x2) (i 2))
                          (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                             (if_then_else_M
                                (EQ_M (reveal x3) (i 2)) &
                                (EQ_M (to x1) (i 2)) qa1002
                                (if_then_else_M (EQ_M (to x3) (i 1)) qc2001 O)))
                          O))))

 (if_then_else_M (Bvar 1)
                 (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                    (if_then_else_M
                       (EQ_M (reveal x2) (i 1)) & (Bvar 1)
                       (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                          (if_then_else_M
                             (EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)
                             qa0120 O))
                       (if_then_else_M
                          (EQ_M (to x2) (i 2)) & (EQ_M (act x2) new)
                          (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                             (if_then_else_M
                                (EQ_M (reveal x3) (i 1)) &
                                (Bvar 1) qa0120
                                (if_then_else_M
                                   (EQ_M (reveal x3) (i 1)) &
                                   (EQ_M (to x2) (i 1)) qa0120
                                   (if_then_else_M 
                                      (EQ_M (to x3) (i 2)) qc0210 O)))) O)))
                 (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 2)
                    (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                       (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                          (if_then_else_M (EQ_M (to x2) (i 2))
                             (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                (if_then_else_M
                                   ((((EQ_M (reveal x3) (i 2)) &
                                      (EQ_M (to x2) (i 2))) &
                                     (EQ_M (to x1) (i 2))) &
                                    (notb (EQ_M (act x2) new))) &
                                   (Bvar 2) qa0300
                                   (if_then_else_M 
                                      (EQ_M (to x3) (i 1)) qc0210 O)))
                             (if_then_else_M (EQ_M (to x2) (i 1))
                                (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                                   (if_then_else_M
                                      (EQ_M (reveal x3) (i 1)) &
                                      (Bvar 1) qa0120
                                      (if_then_else_M
                                         (EQ_M (reveal x3) (i 1)) &
                                         (EQ_M (to x2) (i 1)) qa0120
                                         (if_then_else_M 
                                            (EQ_M (to x3) (i 2)) qc0210 O))))
                                O))))
                    (if_then_else_M (EQ_M (to x1) (i 2))
                       (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                          (if_then_else_M
                             (EQ_M (reveal x2) (i 1)) & (Bvar 1)
                             (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                (if_then_else_M
                                   (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                                   qa1002 O))
                             (if_then_else_M
                                (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                   (if_then_else_M
                                      (EQ_M (reveal x3) (i 2)) &
                                      (EQ_M (to x1) (i 2)) qa1002
                                      (if_then_else_M 
                                         (EQ_M (to x3) (i 1)) qc2001 O))) O)))
                       O)))).

simpl in H0.

repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (if_then_else_B
                                          (EQ_M (reveal (f mphi2)) (i 1))
                                          (EQ_M (to (f mphi1)) (i 1)) FAlse)) in H1. simpl in H1.  rewrite H1 in H0.
clear H1.
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (if_then_else_B
                                    (if_then_else_B
                                       (EQ_M (reveal (f mphi2)) (i 1))
                                       (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                    (if_then_else_B
                                       (EQ_M (act (f mphi1)) new) FAlse TRue)
                                    FAlse)
) in H1. simpl in H1.  rewrite H1 in H0.
clear H1.

pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (reveal (f mphi1)) (i 1))) in H1. simpl in H1.  rewrite H1 in H0.
clear H1.

pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (reveal (f mphi2)) (i 1))) in H1. simpl in H1.  rewrite H1 in H0.
clear H1.


(***************H***************************************************************)
(********************************************************************************)
 
pose proof( IFEVAL_M (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2)) O
                          (if_then_else_M
                             (if_then_else_B
                                (if_then_else_B
                                   (if_then_else_B
                                      (EQ_M (reveal (f mphi2)) (i 1))
                                      (Bvar 0) FAlse)
                                   (if_then_else_B 
                                      (EQ_M (act (f mphi1)) new) FAlse TRue)
                                   FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                             (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
                                O
                                (if_then_else_M (EQ_M (to (f mphi3)) (i 2))
                                   (exp (pi1 (ggen (N 0))) 
                                      (pi2 (ggen (N 0))) 
                                      (r (N 4))) O))
                             (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
                                (if_then_else_M
                                   (if_then_else_B
                                      (EQ_M (reveal (f mphi3)) (i 2))
                                      (EQ_M (to (f mphi0)) (i 2)) FAlse)
                                   (exp (pi1 (ggen (N 0))) 
                                      (m (f mphi0)) 
                                      (r (N 1)))
                                   (if_then_else_M
                                      (if_then_else_B
                                         (EQ_M (reveal (f mphi3)) (i 2))
                                         (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi2)) 
                                         (r (N 3)))
                                      (if_then_else_M
                                         (if_then_else_B
                                            (if_then_else_B
                                               (if_then_else_B
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 1))
                                                  (Bvar 0)
                                                  FAlse)
                                                  (EQ_M (to (f mphi0)) (i 1))
                                                  FAlse)
                                               (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse TRue) FAlse)
                                            (EQ_M (act (f mphi0)) new) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi1)) 
                                            (r (N 1))) O))) O))) 


(if_then_else_M (EQ_M (to (f mphi1)) (i 2))
                          (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1)) O
                             (if_then_else_M
                                (if_then_else_B
                                   (EQ_M (reveal (f mphi2)) (i 2))
                                   (EQ_M (to (f mphi0)) (i 2)) FAlse)
                                (if_then_else_M
                                   (EQ_M (reveal (f mphi3)) (i 1)) O
                                   (if_then_else_M
                                      (EQ_M (to (f mphi3)) (i 1)) acc O))
                                (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                                   (if_then_else_M
                                      (if_then_else_B
                                         (EQ_M (reveal (f mphi3)) (i 2))
                                         (EQ_M (to (f mphi0)) (i 2)) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi0)) 
                                         (r (N 1)))
                                      (if_then_else_M
                                         (if_then_else_B
                                            (EQ_M (reveal (f mphi3)) (i 2))
                                            (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi2)) 
                                            (r (N 3)))
                                         (if_then_else_M
                                            (if_then_else_B
                                               (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 1))
                                                  (Bvar 0)
                                                  FAlse)
                                                  (EQ_M (to (f mphi0)) (i 1))
                                                  FAlse)
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse TRue) FAlse)
                                               (EQ_M (act (f mphi0)) new)
                                               FAlse)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 1))) O))) O))) O) 0).


simpl in H1.


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (EQ_M (reveal (f mphi2)) (i 1))) in H2. simpl in H2.  rewrite H2 in H1.
clear H2.

repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (EQ_M (reveal (f mphi3)) (i 1))) in H2. simpl in H2.  rewrite H2 in H1.
clear H2.
apply Forall_ELM_EVAL_M with (n:=0) (x:=  EQ_M (to (f mphi1)) (i 1)) in H1. simpl in H1.


pose proof (b1_notb2 0 ).
simpl in H2.

apply Forall_ELM_EVAL_B with (n:=0) (b:= (EQ_M (reveal (f mphi2)) (i 1))) in H2. simpl in H2.

apply Forall_ELM_EVAL_B with (n:=1) (b:= (EQ_M (act (f mphi1)) new)) in H2. simpl in H2. rewrite H2 in H1; clear H2.



pose proof (b1_notb2 0 ).
simpl in H2.

apply Forall_ELM_EVAL_B with (n:=0) (b:=  (if_then_else_B
                                       (EQ_M (reveal (f mphi3)) (i 1))
                                       (EQ_M (to (f mphi0)) (i 1)) FAlse)) in H2. simpl in H2.

apply Forall_ELM_EVAL_B with (n:=1) (b:=  (EQ_M (act (f mphi1)) new)) in H2. simpl in H2. rewrite H2 in H1; clear H2.

rewrite H1 in H; clear H1.

(****************************(EQ_M (to (f mphi1)) (i 2))
                          (EQ_M (act (f mphi1)) new)************************)

pose proof (mor_eval_andB 1  (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2)) O
                          (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1))
                             (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
                                O
                                (if_then_else_M (Bvar 1)
                                   acc O))
                             (if_then_else_M
                                (if_then_else_B
                                   (EQ_M (reveal (f mphi2)) (i 1))
                                   (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                (if_then_else_M
                                   (EQ_M (reveal (f mphi3)) (i 2)) O
                                   (if_then_else_M
                                      (Bvar 1) acc O))
                                (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
                                   (if_then_else_M
                                      (if_then_else_B
                                         (EQ_M (reveal (f mphi3)) (i 1))
                                         (EQ_M (to (f mphi0)) (i 1)) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi0)) 
                                         (r (N 1)))
                                      (if_then_else_M
                                         (if_then_else_B
                                            (EQ_M (reveal (f mphi3)) (i 1))
                                            (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi1)) 
                                            (r (N 2)))
                                         (if_then_else_M
                                            (if_then_else_B
                                               (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (Bvar 1)
                                                  FAlse)
                                                  (EQ_M (to (f mphi0)) (i 2))
                                                  FAlse)
                                                  (if_then_else_B
                                                 (Bvar 2)
                                                  FAlse TRue) FAlse)
                                               (EQ_M (act (f mphi0)) new)
                                               FAlse)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 1)))
                                            (if_then_else_M
                                               (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (EQ_M (to (f mphi2)) (i 2))
                                                  FAlse)
                                                  (Bvar 1)
                                                  FAlse)
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse TRue) FAlse)
                                                 (Bvar 2)
                                                  FAlse)
                                               (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (m (f mphi2)) 
                                                  (r (N 2))) O)))) O)))) O).
simpl in H1.
repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=   (if_then_else_B
                                                (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                (EQ_M (to (f mphi2)) (i 2))
                                                FAlse)) in H2. simpl in H2.  rewrite H2 in H1.
clear H2.

pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (if_then_else_B
                                          (if_then_else_B
                                             (EQ_M (reveal (f mphi3)) (i 2))
                                             (EQ_M (to (f mphi2)) (i 2))
                                             FAlse)
                                          (if_then_else_B
                                             (EQ_M (act (f mphi2)) new) FAlse
                                             TRue) FAlse)) in H2. simpl in H2.  rewrite H2 in H1.
clear H2.


apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x2) (i 2))) in H1.
 simpl in H1.

apply Forall_ELM_EVAL_M with (n:=2) (x:=   (EQ_M (act x2) new)) in H1.
simpl in H1.


(**************EQ_M (reveal (f mphi2)) (i 1))*******************************)
pose proof(IFEVAL_M (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2)) O acc)
(if_then_else_M
                        (if_then_else_B (Bvar 0)
                           (EQ_M (to (f mphi1)) (i 1)) FAlse)
                        (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2)) O acc)
                        (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
                           (if_then_else_M
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                 (EQ_M (to (f mphi0)) (i 1)) FAlse)
                              (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                              (if_then_else_M
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi1)) (r (N 2)))
                                 (if_then_else_M
                                    (if_then_else_B
                                       (if_then_else_B
                                          (EQ_M (reveal (f mphi3)) (i 2))
                                          (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                       (if_then_else_B
                                          (EQ_M (act (f mphi2)) new) FAlse
                                          TRue) FAlse)
                                    (exp (pi1 (ggen (N 0))) 
                                       (m (f mphi2)) 
                                       (r (N 2))) O))) O)) 0).

simpl in H2.



repeat (try rewrite IFTRUE_M in H2; try rewrite IFFALSE_M in H2; try rewrite IFSAME_M in H2;try rewrite IFTRUE_B in H2; try rewrite IFFALSE_B in H2; try rewrite IFSAME_B in H2).

apply Forall_ELM_EVAL_M with (n:=0) (x:=   EQ_M (reveal (f mphi2)) (i 1)) in H2.
simpl in H2.



rewrite H2 in H1.





(*************(EQ_M (to (f mphi2)) (i 2))***************)
pose proof(IFEVAL_M (if_then_else_M
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                  (if_then_else_M
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                        (EQ_M (to (f mphi1)) (i 1)) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 2)))
                     (if_then_else_M
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                              (Bvar 0) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                              TRue) FAlse)
                        (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r (N 2))) O))) O 0).
simpl in H3.

repeat (try rewrite IFTRUE_M in H3; try rewrite IFFALSE_M in H3; try rewrite IFSAME_M in H3;try rewrite IFTRUE_B in H3; try rewrite IFFALSE_B in H3; try rewrite IFSAME_B in H3).
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=   (EQ_M (reveal (f mphi3)) (i 2))) in H4. simpl in H4.  rewrite H4 in H3.
clear H4.
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (to (f mphi2)) (i 2))  ) in H3. simpl in H3.
 
pose proof (b1_notb2 0 ).
simpl in H4.


apply Forall_ELM_EVAL_B with (n:=0) (b:=   (EQ_M (reveal (f mphi3)) (i 2))) in H4. simpl in H4.
apply Forall_ELM_EVAL_B with (n:=1) (b:=  (EQ_M (act (f mphi2)) new) ) in H4. simpl in H4. rewrite H4 in H3; clear H4.

rewrite H3 in H1. 

clear H3. clear H2.


(*******************************************************************)

(*****************************(EQ_M (reveal (f mphi3)) (i 1))
                     (EQ_M (to (f mphi0)) (i 1)) *****)


pose proof (mor_eval_andB 1 (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))  

 (if_then_else_M
                     (if_then_else_B (Bvar 1)
                        (EQ_M (to (f mphi1)) (i 1)) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 2)))
                     (if_then_else_M
                        (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse
                           (EQ_M (reveal (f mphi3)) (i 2)))
                        (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r (N 2))) O))).

simpl in H2.

repeat (try rewrite IFTRUE_M in H2; try rewrite IFFALSE_M in H2; try rewrite IFSAME_M in H2;try rewrite IFTRUE_B in H2; try rewrite IFFALSE_B in H2; try rewrite IFSAME_B in H2).
apply Forall_ELM_EVAL_M with (n:=1) (x:= (EQ_M (reveal (f mphi3)) (i 1)) ) in H2.
 simpl in H2.

apply Forall_ELM_EVAL_M with (n:=2) (x:=    (EQ_M (to (f mphi0)) (i 1))) in H2.
 simpl in H2.
rewrite H2 in H1; clear H2.

rewrite H1 in H. clear H1.


(**************************(EQ_M (reveal (f mphi3)) (i 2))
                                      (EQ_M (to (f mphi0)) (i 2)) ***********)

pose proof(mor_eval_andB 1 (exp (pi1 (ggen (N 0))) 
                                      (m (f mphi0)) 
                                      (r (N 1)))  (if_then_else_M
                                      (if_then_else_B
                                         (Bvar 1)
                                         (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi2)) 
                                         (r (N 3)))
                                      (if_then_else_M
                                         (if_then_else_B
                                            (if_then_else_B
                                               (EQ_M (act (f mphi1)) new)
                                               FAlse
                                               (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 1))
                                                  (EQ_M (to (f mphi0)) (i 1))
                                                  FAlse))
                                            (EQ_M (act (f mphi0)) new) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi1)) 
                                            (r (N 1))) O)) ).

simpl in H1.

repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).


apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (reveal (f mphi3)) (i 2))  ) in H1.


apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (to (f mphi0)) (i 2))) in H1.
simpl in H1.
rewrite H1 in H.
clear H1.


(*(if_then_else_B (EQ_M (act (f mphi1)) new)
                                   FAlse (EQ_M (reveal (f mphi2)) (i 1))) and
                                (EQ_M (act (f mphi0)) new) *)


pose proof ( mor_eval_andB 1 (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
                                O
                                (if_then_else_M (EQ_M (to (f mphi3)) (i 2))
                                   (exp (pi1 (ggen (N 0))) 
                                      (pi2 (ggen (N 0))) 
                                      (r (N 4))) O))   (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
                                (if_then_else_M
                                   (EQ_M (reveal (f mphi3)) (i 2))
                                   (if_then_else_M
                                      (EQ_M (to (f mphi0)) (i 2))
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi0)) 
                                         (r (N 1)))
                                      (if_then_else_M
                                         (EQ_M (to (f mphi2)) (i 2))
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi2)) 
                                            (r (N 3)))
                                         (if_then_else_M
                                            (if_then_else_B
                                               (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 1))
                                                  (EQ_M (to (f mphi0)) (i 1))
                                                  FAlse))
                                              (Bvar 2)
                                               FAlse)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 1))) O)))
                                   (if_then_else_M
                                      (if_then_else_B
                                         (if_then_else_B
                                            (EQ_M (act (f mphi1)) new) FAlse
                                            (if_then_else_B
                                               (EQ_M (reveal (f mphi3)) (i 1))
                                               (EQ_M (to (f mphi0)) (i 1))
                                               FAlse))
                                         (Bvar 2) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi1)) 
                                         (r (N 1))) O)) O)).
simpl in H1.                      

repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).


apply Forall_ELM_EVAL_M with (n:=1) (x:=  (if_then_else_B (EQ_M (act (f mphi1)) new)
                                   FAlse (EQ_M (reveal (f mphi2)) (i 1))) ) in H1.


apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (act (f mphi0)) new)) in H1.
simpl in H1.
rewrite H1 in H.
clear H1.


(********************************************EQ_M (to (f mphi2)) (i 2))********)

pose proof (IFEVAL_M (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
                  (if_then_else_M (EQ_M (to (f mphi0)) (i 2))
                     (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                     (if_then_else_M (Bvar 0)
                        (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r (N 3)))
                        (if_then_else_M
                           (if_then_else_B
                              (if_then_else_B (EQ_M (act (f mphi1)) new)
                                 FAlse
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 1))
                                    (EQ_M (to (f mphi0)) (i 1)) FAlse))
                              (EQ_M (act (f mphi0)) new) FAlse)
                           (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 1))) O)))
                  (if_then_else_M
                     (if_then_else_B
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi0)) (i 1)) FAlse))
                        (EQ_M (act (f mphi0)) new) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 1))) O)) O 0).


simpl in H1.

repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
apply Forall_ELM_EVAL_M with (n:=0) (x:= EQ_M (to (f mphi2)) (i 2))  in H1.
simpl in H1.
rewrite H1 in H.

clear H1.






(***********************(EQ_M (to (f mphi0)) (i 2))******)

pose proof (IFEVAL_M (if_then_else_M (EQ_M (reveal (f mphi1)) (i 1)) O
                    (if_then_else_M
                       (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
                          (EQ_M (act (f mphi1)) new) FAlse)
                       (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1)) O
                          (if_then_else_M
                             (if_then_else_B (EQ_M (reveal (f mphi2)) (i 2))
                                (Bvar 0) FAlse)
                             (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1))
                                O
                                (if_then_else_M (EQ_M (to (f mphi3)) (i 1))
                                   acc O))
                             (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                                (if_then_else_M
                                   (if_then_else_B
                                      (EQ_M (reveal (f mphi3)) (i 2))
                                      (Bvar 0) FAlse)
                                   (exp (pi1 (ggen (N 0))) 
                                      (m (f mphi0)) 
                                      (r (N 1)))
                                   (if_then_else_M
                                      (if_then_else_B
                                         (EQ_M (reveal (f mphi3)) (i 2))
                                         (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi2)) 
                                         (r (N 3)))
                                      (if_then_else_M
                                         (if_then_else_B
                                            (if_then_else_B
                                               (if_then_else_B
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 1))
                                                  (EQ_M (to (f mphi1)) (i 1))
                                                  FAlse)
                                                  (EQ_M (to (f mphi0)) (i 1))
                                                  FAlse)
                                               (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse TRue) FAlse)
                                            (EQ_M (act (f mphi0)) new) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi1)) 
                                            (r (N 1))) O))) O))) O)) O 0) .
simpl in H1.


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (EQ_M (reveal (f mphi2)) (i 2))) in H2. simpl in H2.  rewrite H2 in H1.
clear H2.

pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (reveal (f mphi3)) (i 2)) ) in H2. simpl in H2.  rewrite H2 in H1.
clear H2.
repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
apply Forall_ELM_EVAL_M with (n:=0) (x:= EQ_M (to (f mphi0)) (i 2))  in H1.
simpl in H1.



(*********************(EQ_M (reveal (f mphi3)) (i 2))********)

pose proof (IFEVAL_M (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                              (if_then_else_M
                                 (if_then_else_B
                                    (Bvar 0)
                                    (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi2)) (r (N 3)))
                                 (if_then_else_M
                                    (if_then_else_B
                                       (if_then_else_B
                                          (if_then_else_B
                                             (if_then_else_B
                                                (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 1))
                                                (EQ_M (to (f mphi1)) (i 1))
                                                FAlse)
                                             (EQ_M (to (f mphi0)) (i 1))
                                             FAlse)
                                          (if_then_else_B
                                             (EQ_M (act (f mphi1)) new) FAlse
                                             TRue) FAlse)
                                       (EQ_M (act (f mphi0)) new) FAlse)
                                    (exp (pi1 (ggen (N 0))) 
                                       (m (f mphi1)) 
                                       (r (N 1))) O)) 0).
simpl in H2.

repeat (try rewrite IFTRUE_M in H2; try rewrite IFFALSE_M in H2; try rewrite IFSAME_M in H2;try rewrite IFTRUE_B in H2; try rewrite IFFALSE_B in H2; try rewrite IFSAME_B in H2).

apply Forall_ELM_EVAL_M with (n:=0) (x:= EQ_M (reveal (f mphi3)) (i 2))  in H2.
simpl in H2.
rewrite H2 in H1.

clear H2.


(**************************(EQ_M (to (f mphi1)) (i 1))
                     (EQ_M (act (f mphi1)) new)***********)

 pose proof ( mor_eval_andB 1 (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1)) O
                     (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2))
                        (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                           (if_then_else_M (EQ_M (to (f mphi3)) (i 1)) acc O))
                        (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                           (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
                              (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                              (if_then_else_M
                                 (if_then_else_B
                                    (if_then_else_B
                                       (if_then_else_B
                                          (if_then_else_B
                                             (EQ_M (reveal (f mphi3)) (i 1))
                                             (Bvar 1)
                                             FAlse)
                                          (EQ_M (to (f mphi0)) (i 1)) FAlse)
                                       (if_then_else_B
                                         (Bvar 2) FAlse
                                          TRue) FAlse)
                                    (EQ_M (act (f mphi0)) new) FAlse)
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi1)) (r (N 1))) O)) O))) O ).

simpl in H2.

repeat (try rewrite IFTRUE_M in H2; try rewrite IFFALSE_M in H2; try rewrite IFSAME_M in H2;try rewrite IFTRUE_B in H2; try rewrite IFFALSE_B in H2; try rewrite IFSAME_B in H2).

apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to (f mphi1)) (i 1))) in H2.


apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (act (f mphi1)) new) ) in H2.
simpl in H2.
rewrite H2 in H1.
rewrite H1 in H.
clear H2. clear H1.

(********************************(EQ_M (to (f mphi1)) (i 1))*********)

pose proof(IFEVAL_M  (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2)) O
                             (if_then_else_M
                                (if_then_else_B
                                   (EQ_M (reveal (f mphi2)) (i 1))
                                   (Bvar 0) FAlse)
                                (if_then_else_M
                                   (EQ_M (reveal (f mphi3)) (i 2)) O
                                   (if_then_else_M
                                      (EQ_M (to (f mphi1)) (i 2)) acc O))
                                (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
                                   (if_then_else_M
                                      (if_then_else_B
                                         (EQ_M (reveal (f mphi3)) (i 1))
                                         (EQ_M (to (f mphi0)) (i 1)) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi0)) 
                                         (r (N 1)))
                                      (if_then_else_M
                                         (if_then_else_B
                                            (EQ_M (reveal (f mphi3)) (i 1))
                                            (Bvar 0) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi1)) 
                                            (r (N 2)))
                                         (if_then_else_M
                                            (if_then_else_B
                                               (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (EQ_M (to (f mphi1)) (i 2))
                                                  FAlse)
                                                  (EQ_M (to (f mphi0)) (i 2))
                                                  FAlse)
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse TRue) FAlse)
                                               (EQ_M (act (f mphi0)) new)
                                               FAlse)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 1)))
                                            (if_then_else_M
                                               (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (EQ_M (to (f mphi2)) (i 2))
                                                  FAlse)
                                                  (EQ_M (to (f mphi1)) (i 2))
                                                  FAlse)
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse TRue) FAlse)
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse)
                                               (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (m (f mphi2)) 
                                                  (r (N 2))) O)))) O))) O 0).


simpl in H1.






repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (reveal (f mphi2)) (i 1))) in H2. simpl in H2.  rewrite H2 in H1.
clear H2.



apply Forall_ELM_EVAL_M with (n:=0) (x:=  (EQ_M (to (f mphi1)) (i 1) )) in H1.
simpl in H1. 




(**************************(EQ_M (to (f mphi2)) (i 2))****************************)

pose proof(IFEVAL_M (if_then_else_M
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                        (if_then_else_M
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              TRue FAlse)
                           (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 2)))
                           (if_then_else_M
                              (if_then_else_B
                                 (if_then_else_B
                                    (if_then_else_B
                                       (if_then_else_B
                                          (EQ_M (reveal (f mphi3)) (i 2))
                                          (EQ_M (to (f mphi1)) (i 2)) FAlse)
                                       (EQ_M (to (f mphi0)) (i 2)) FAlse)
                                    (if_then_else_B
                                       (EQ_M (act (f mphi1)) new) FAlse TRue)
                                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                              (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 1)))
                              (if_then_else_M
                                 (if_then_else_B
                                    (if_then_else_B
                                       (if_then_else_B
                                          (if_then_else_B
                                             (EQ_M (reveal (f mphi3)) (i 2))
                                             (Bvar 0)
                                             FAlse)
                                          (EQ_M (to (f mphi1)) (i 2)) FAlse)
                                       (if_then_else_B
                                          (EQ_M (act (f mphi2)) new) FAlse
                                          TRue) FAlse)
                                    (EQ_M (act (f mphi1)) new) FAlse)
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi2)) (r (N 2))) O)))) O 0).


simpl in H2. 

apply Forall_ELM_EVAL_M with (n:=0) (x:=  (EQ_M (to (f mphi2)) (i 2))) in H2.
simpl in H2.



repeat (try rewrite IFTRUE_M in H2; try rewrite IFFALSE_M in H2; try rewrite IFSAME_M in H2;try rewrite IFTRUE_B in H2; try rewrite IFFALSE_B in H2; try rewrite IFSAME_B in H2).

pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (reveal (f mphi3)) (i 2))) in H3. simpl in H3.  rewrite H3 in H2.
clear H3.









(*************************** (EQ_M (reveal (f mphi3)) (i 1))
                  (EQ_M (to (f mphi0)) (i 1))*********)

      pose proof (   mor_eval_andB 1  
               (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
               (if_then_else_M
                  (if_then_else_B (Bvar 1) TRue FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 2)))
                  (if_then_else_M
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                                 (EQ_M (to (f mphi1)) (i 2)) FAlse)
                              (EQ_M (to (f mphi0)) (i 2)) FAlse)
                           (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse
                              TRue) FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                     (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 1)))
                     (if_then_else_M
                        (if_then_else_B
                           (if_then_else_B
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                                 (EQ_M (to (f mphi1)) (i 2)) FAlse)
                              (if_then_else_B (EQ_M (act (f mphi2)) new)
                                 FAlse TRue) FAlse)
                           (EQ_M (act (f mphi1)) new) FAlse)
                        (exp (pi1 (ggen (N 0))) (m (f mphi2)) (r (N 2))) O))) ).

simpl in H3.            

repeat (try rewrite IFTRUE_M in H3; try rewrite IFFALSE_M in H3; try rewrite IFSAME_M in H3;try rewrite IFTRUE_B in H3; try rewrite IFFALSE_B in H3; try rewrite IFSAME_B in H3).

apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (reveal (f mphi3)) (i 1))) in H3.


apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (to (f mphi0)) (i 1)) ) in H3.
simpl in H3.
pose proof(IFMORPH_B2 0
(EQ_M (to (f mphi1)) (i 2)) FAlse
                        (EQ_M (to (f mphi0)) (i 2)) FAlse).
rewrite IFFALSE_B in H4.
apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (reveal (f mphi3)) (i 2)) ) in H4.
simpl in H4.
(*
pose proof(IFMORPH_B1 (EQ_M (to (f mphi0)) (i 2)) FAlse FAlse  0 1 ).
rewrite IFSAME_B in H5.

apply Forall_ELM_EVAL_B with (n:=1) (b:= (EQ_M (reveal (f mphi3)) (i 2))  ) in H5.
simpl in H5.

apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (to (f mphi1)) (i 2))) in H5.
simpl in H5.
rewrite H5 in H4.
*)

rewrite H4 in H3.
rewrite H2 in H1.
clear H2 ;clear H3; clear H4. 
rewrite H1 in H.
clear H1.
clear H0.


(***************************************)


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (EQ_M (reveal (f mphi3)) (i 1))) in H0. simpl in H0.  rewrite H0 in H.

clear H0.
rewrite H.

pose proof(IFMORPH_B2 0 (EQ_M (to (f mphi1)) (i 2))
                                                  FAlse
                                                  (EQ_M (to (f mphi0)) (i 2))
                                                  FAlse ).

simpl in H0.
rewrite IFFALSE_B in H0.
apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2)) ) in H0.
simpl in H0.
rewrite H0 . clear H0.



pose proof(IFMORPH_B1 (EQ_M (to (f mphi0)) (i 2)) FAlse FAlse  0 1 ).
rewrite IFSAME_B in H0.

apply Forall_ELM_EVAL_B with (n:=1) (b:= (EQ_M (reveal (f mphi3)) (i 2))  ) in H0.
simpl in H0.

apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (to (f mphi1)) (i 2))) in H0.
simpl in H0.
rewrite H0 .
clear H0. 
(*****************************)
pose proof(IFMORPH_B2 0 (EQ_M (to (f mphi1)) (i 2))
                                                  FAlse
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse TRue) FAlse ).

simpl in H0.
rewrite IFFALSE_B in H0.
apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2)) ) in H0.
simpl in H0.
rewrite H0. clear H0.



pose proof(IFMORPH_B2 0  (if_then_else_B
                                                  (EQ_M (to (f mphi1)) (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse TRue) FAlse) FAlse
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse).
simpl in H0.
rewrite IFFALSE_B in H0.
apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2)) ) in H0.
simpl in H0.
rewrite H0. clear H0.


(**************************)

pose proof(IFMORPH_B2 0  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse TRue) FAlse
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse).
simpl in H0.
rewrite IFFALSE_B in H0.
apply Forall_ELM_EVAL_B with (n:=0) (b:=   (EQ_M (to (f mphi1)) (i 2)) ) in H0.
simpl in H0.
rewrite H0 . clear H0.

pose proof(IFMORPH_B2 0  FAlse TRue
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse).
simpl in H0.
rewrite IFFALSE_B in H0.
rewrite IFTRUE_B in H0.
apply Forall_ELM_EVAL_B with (n:=0) (b:=    (EQ_M (act (f mphi2)) new) ) in H0.
simpl in H0.
rewrite H0 . clear H0.


pose proof(IFMORPH_B2 0  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (EQ_M (to (f mphi0)) (i 2))
                                                  FAlse) FAlse
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse TRue) FAlse).
simpl in H0.
rewrite IFFALSE_B in H0.






apply Forall_ELM_EVAL_B with (n:=0) (b:=    (EQ_M (to (f mphi1)) (i 2)) ) in H0.
simpl in H0.
rewrite H0 .
pose proof(IFMORPH_B2 1 (EQ_M (to (f mphi0)) (i 2)) FAlse
                (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue) FAlse).
simpl in H1.
rewrite IFFALSE_B in H1.

apply Forall_ELM_EVAL_B with (n:=1) (b:=    (EQ_M (reveal (f mphi3)) (i 2)) ) in H1.
simpl in H1.
rewrite H1 . clear H1.


 clear H0.
(************************)
pose proof(IFMORPH_B2 0  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (to (f mphi0)) (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse TRue) FAlse) FAlse)
                                                  FAlse
                                               (EQ_M (act (f mphi0)) new)
                                               FAlse).
simpl in H0.
rewrite IFFALSE_B in H0.
apply Forall_ELM_EVAL_B with (n:=0) (b:=   (EQ_M (to (f mphi1)) (i 2))) in H0.
simpl in H0. 
rewrite H0   .

clear H0.
(***********************************)


pose proof(IFMORPH_B1  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi1)) new))
                                                  FAlse FAlse  0 1 ).
rewrite IFSAME_B in H0.

apply Forall_ELM_EVAL_B with (n:=1) (b:= (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))  ) in H0.
simpl in H0.

apply Forall_ELM_EVAL_B with (n:=0) (b:=    (EQ_M (to (f mphi1)) (i 2))) in H0.
simpl in H0.
rewrite H0     .
clear H0.


pose proof(IFMORPH_B1 (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi1)) new))
                                                  FAlse FAlse  0 1 ).
rewrite IFSAME_B in H0.

apply Forall_ELM_EVAL_B with (n:=1) (b:=  (EQ_M (to (f mphi1)) (i 2))  ) in H0.
simpl in H0.

apply Forall_ELM_EVAL_B with (n:=0) (b:=    (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))) in H0.
simpl in H0.
rewrite H0     .
clear H0. 
(****************************)



pose proof(IFMORPH_B2 0  (if_then_else_B
                                                  (EQ_M (to (f mphi0)) (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse TRue) FAlse) FAlse
                                                  (EQ_M (act (f mphi0)) new)
                                                  FAlse).
simpl in H0.
rewrite IFFALSE_B in H0.
apply Forall_ELM_EVAL_B with (n:=0) (b:=   (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))) in H0.
simpl in H0. 
rewrite H0     .

clear H0.






pose proof(IFMORPH_B2 0  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse TRue) FAlse
                                                  (EQ_M (act (f mphi0)) new)
                                                  FAlse).
simpl in H0.
rewrite IFFALSE_B in H0.
apply Forall_ELM_EVAL_B with (n:=0) (b:=   (EQ_M (to (f mphi0)) (i 2))) in H0.
simpl in H0. 
rewrite H0     .

clear H0.





pose proof(IFMORPH_B2 0   FAlse TRue
                                                  (EQ_M (act (f mphi0)) new)
                                                  FAlse ).
simpl in H0.
rewrite IFFALSE_B in H0. rewrite IFTRUE_B in H0.
apply Forall_ELM_EVAL_B with (n:=0) (b:=   (EQ_M (act (f mphi1)) new)) in H0.
simpl in H0. 
rewrite H0     .

clear H0.



(**************(EQ_M (to (f mphi0)) (i 2))
                 (EQ_M (act x1) new)*****)


pose proof(mor_eval_andB 1 (if_then_else_M (EQ_M (reveal (f mphi1)) (i 1)) O
                 (if_then_else_M (EQ_M (reveal (f mphi1)) (i 2)) O
                    (if_then_else_M (EQ_M (to (f mphi1)) (i 2))
                       (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1)) O
                          (if_then_else_M
                             (if_then_else_B
                                (if_then_else_B
                                   (if_then_else_B
                                      (if_then_else_B
                                         (EQ_M (reveal (f mphi2)) (i 2))
                                         (EQ_M (to (f mphi1)) (i 2)) FAlse)
                                      (Bvar 1) FAlse)
                                   (if_then_else_B 
                                      (EQ_M (act (f mphi1)) new) FAlse TRue)
                                   FAlse)(Bvar 2) FAlse)
                             (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1))
                                O
                                (if_then_else_M (EQ_M (to (f mphi3)) (i 1))
                                   (exp (pi1 (ggen (N 0))) 
                                      (pi2 (ggen (N 0))) 
                                      (r (N 4))) O))
                             (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                                (if_then_else_M
                                   (if_then_else_B
                                      (EQ_M (reveal (f mphi3)) (i 1))
                                      (EQ_M (to (f mphi0)) (i 1)) FAlse)
                                   (exp (pi1 (ggen (N 0))) 
                                      (m (f mphi0)) 
                                      (r (N 1)))
                                   (if_then_else_M
                                      (if_then_else_B
                                         (EQ_M (reveal (f mphi3)) (i 1))
                                         (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi1)) 
                                         (r (N 2)))
                                      (if_then_else_M
                                         (if_then_else_B
                                            (EQ_M (to (f mphi1)) (i 2))
                                            (if_then_else_B
                                               (EQ_M (reveal (f mphi3)) (i 2))
                                               (if_then_else_B
                                                  (Bvar 1)
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi0)) new))
                                                  FAlse) FAlse) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi1)) 
                                            (r (N 1)))
                                         (if_then_else_M
                                            (if_then_else_B
                                               (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (EQ_M (to (f mphi2)) (i 2))
                                                  FAlse)
                                                  (EQ_M (to (f mphi1)) (i 2))
                                                  FAlse)
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse TRue) FAlse)
                                               (EQ_M (act (f mphi1)) new)
                                               FAlse)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi2)) 
                                               (r (N 2))) O)))) O)))
                       (if_then_else_M (EQ_M (to (f mphi1)) (i 1))
                          (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2)) O
                             (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1))
                                (if_then_else_M
                                   (EQ_M (reveal (f mphi3)) (i 2)) O
                                   (if_then_else_M
                                      (EQ_M (to (f mphi1)) (i 2)) acc O))
                                (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
                                   (if_then_else_M
                                      (if_then_else_B
                                         (EQ_M (reveal (f mphi3)) (i 1))
                                         (EQ_M (to (f mphi0)) (i 1)) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi0)) 
                                         (r (N 1)))
                                      (if_then_else_M
                                         (EQ_M (reveal (f mphi3)) (i 1))
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi1)) 
                                            (r (N 2)))
                                         (if_then_else_M
                                            (if_then_else_B
                                               (EQ_M (to (f mphi1)) (i 2))
                                               (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (if_then_else_B
                                                  (Bvar 1)
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi0)) new))
                                                  FAlse) FAlse) FAlse)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 1)))
                                            (if_then_else_M
                                               (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (to (f mphi1)) (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi1)) new))
                                                  FAlse) FAlse)
                                               (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (m (f mphi2)) 
                                                  (r (N 2))) O)))) O))) O))))  

(if_then_else_M (Bvar 1)
                 (if_then_else_M (EQ_M (reveal (f mphi1)) (i 1)) O
                    (if_then_else_M (EQ_M (to (f mphi1)) (i 1))
                       (if_then_else_M (EQ_M (act (f mphi1)) new)
                          (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1)) O
                             (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2))
                                (if_then_else_M
                                   (EQ_M (reveal (f mphi3)) (i 1)) O
                                   (if_then_else_M
                                      (EQ_M (to (f mphi3)) (i 1)) acc O))
                                (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                                   (if_then_else_M
                                      (EQ_M (reveal (f mphi3)) (i 2))
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi0)) 
                                         (r (N 1))) O) O))) O) O)) O) ).



 

simpl in H0.

repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (if_then_else_B
                                          (EQ_M (reveal (f mphi2)) (i 2))
                                          (EQ_M (to (f mphi1)) (i 2)) FAlse)) in H1. simpl in H1.  rewrite H1 in H0.

clear H1.
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=(if_then_else_B
                                    (if_then_else_B
                                       (EQ_M (reveal (f mphi2)) (i 2))
                                       (EQ_M (to (f mphi1)) (i 2)) FAlse)
                                    (if_then_else_B
                                       (EQ_M (act (f mphi1)) new) FAlse TRue)
                                    FAlse))
                                    in H1. simpl in H1.  rewrite H1 in H0.

clear H1.

 apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to (f mphi0)) (i 2))) in H0.


apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (act x1) new) ) in H0.
simpl in H0. rewrite H0     .

clear H0.
(*****************(EQ_M (reveal (f mphi3)) (i 2))
                                         (EQ_M (to (f mphi0)) (i 2))*****)

pose proof(mor_eval_andB 1 (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi0)) 
                                         (r (N 1))) (if_then_else_M
                                         (if_then_else_B
                                           (Bvar 1)
                                            (EQ_M (to (f mphi2)) (i 2)) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi2)) 
                                            (r (N 3))) O)).
simpl in H0.
repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).


apply Forall_ELM_EVAL_M with (n:=1) (x:= (EQ_M (reveal (f mphi3)) (i 2)) ) in H0.


apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (to (f mphi0)) (i 2))) in H0.
simpl in H0. rewrite H0     . clear H0.

(*************************(EQ_M (to (f mphi2)) (i 2))**********)


pose proof (IFEVAL_M  (if_then_else_M
                                      (EQ_M (reveal (f mphi3)) (i 2))
                                      (if_then_else_M
                                         (EQ_M (to (f mphi0)) (i 2))
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi0)) 
                                            (r (N 1)))
                                         (if_then_else_M
                                           (Bvar 0)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi2)) 
                                               (r (N 3))) O)) O) O 0);

simpl in H0; repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0); apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (to (f mphi2)) (i 2)) ) in H0; simpl in H0; rewrite H0     ; clear H0.


(*******************************)
pose proof(IFMORPH_B2 0   FAlse
                                            (if_then_else_B
                                               (EQ_M (reveal (f mphi3)) (i 1))
                                               (EQ_M (to (f mphi0)) (i 1))
                                               FAlse)
                                         (EQ_M (act (f mphi0)) new) FAlse);
simpl in H0; rewrite IFFALSE_B in H0; repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0);
apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (act (f mphi1)) new)) in H0;
simpl in H0;rewrite H0     ;clear H0.


pose proof(IFMORPH_B2 0   (EQ_M (to (f mphi0)) (i 1))
                                               FAlse
                                            (EQ_M (act (f mphi0)) new) FAlse);
simpl in H0; rewrite IFFALSE_B in H0; repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0);
apply Forall_ELM_EVAL_B with (n:=0) (b:= (EQ_M (reveal (f mphi3)) (i 1))) in H0;
simpl in H0;rewrite H0     ;clear H0.
(*********************)

pose proof ( IFMORPH_M2 0 FAlse
                                            (EQ_M (reveal (f mphi3)) (i 2)) (exp (pi1 (ggen (N 0)))
                                            (m (f mphi2)) 
                                            (r (N 2))) O) ; simpl in H0.
 repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (act (f mphi2)) new) ) in H0.
simpl in H0;rewrite H0     ;clear H0.

(***************(EQ_M (reveal (f mphi3)) (i 1))
                                            (EQ_M (to (f mphi0)) (i 1)) *******)

pose proof(mor_eval_andB 1   (exp (pi1 (ggen (N 0)))
                                            (m (f mphi0)) 
                                            (r (N 1)))   (if_then_else_M
                                            (Bvar 1)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 2)))
                                            (if_then_else_M
                                               (if_then_else_B
                                                  (EQ_M (to (f mphi1)) (i 2))
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi0)) new))
                                                  FAlse) FAlse)
                                               (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (m (f mphi1)) 
                                                  (r (N 1)))
                                               (if_then_else_M
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (to (f mphi1)) (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi1)) new))
                                                  FAlse) FAlse)
                                                  (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (m (f mphi2)) 
                                                  (r (N 2))) O)))).

repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0);
apply Forall_ELM_EVAL_M with (n:=1) (x:= (EQ_M (reveal (f mphi3)) (i 1)) ) in H0;
apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (to (f mphi0)) (i 1))) in H0;
simpl in H0; rewrite H0     ; clear H0. rewrite IFTRUE_M     . rewrite IFFALSE_M     .

(****************************(EQ_M (to (f mphi1)) (i 2))**************)

 

pose proof(IFEVAL_M (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1)) O
                             (if_then_else_M
                                (if_then_else_B
                                   (if_then_else_B
                                      (EQ_M (reveal (f mphi2)) (i 2))
                                      (Bvar 0) FAlse)
                                   (if_then_else_B 
                                      (EQ_M (act (f mphi1)) new) FAlse TRue)
                                   FAlse)
                                (if_then_else_M
                                   (EQ_M (reveal (f mphi3)) (i 1)) O
                                   (if_then_else_M
                                      (EQ_M (to (f mphi3)) (i 1))
                                      (exp (pi1 (ggen (N 0)))
                                         (pi2 (ggen (N 0))) 
                                         (r (N 4))) O))
                                (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                                   (if_then_else_M
                                      (if_then_else_B
                                         (EQ_M (reveal (f mphi3)) (i 1))
                                         (EQ_M (to (f mphi0)) (i 1)) FAlse)
                                      (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi0)) 
                                         (r (N 1)))
                                      (if_then_else_M
                                         (if_then_else_B
                                            (EQ_M (reveal (f mphi3)) (i 1))
                                            (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi1)) 
                                            (r (N 2)))
                                         (if_then_else_M
                                            (if_then_else_B
                                               (Bvar 0)
                                               (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi0)) new))
                                                  FAlse) FAlse)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 1)))
                                            (if_then_else_M
                                               (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (EQ_M (to (f mphi2)) (i 2))
                                                  FAlse)
                                                  (Bvar 0)
                                                  FAlse)
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse TRue) FAlse)
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse)
                                               (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (m (f mphi2)) 
                                                  (r (N 2))) O)))) O)))




(if_then_else_M (EQ_M (to (f mphi1)) (i 1))
                             (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2))
                                O
                                (if_then_else_M
                                   (EQ_M (reveal (f mphi2)) (i 1))
                                   (if_then_else_M
                                      (EQ_M (reveal (f mphi3)) (i 2)) O
                                      (if_then_else_M
                                         (Bvar 0) acc O))
                                   (if_then_else_M
                                      (EQ_M (to (f mphi2)) (i 2))
                                      (if_then_else_M
                                         (EQ_M (reveal (f mphi3)) (i 1))
                                         (if_then_else_M
                                            (EQ_M (to (f mphi0)) (i 1))
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi0)) 
                                               (r (N 1)))
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 2))))
                                         (if_then_else_M
                                            (if_then_else_B
                                               (Bvar 0)
                                               (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi0)) new))
                                                  FAlse) FAlse)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 1)))
                                            (if_then_else_M
                                               (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (if_then_else_B
                                                  (Bvar 0)
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi1)) new))
                                                  FAlse) FAlse)
                                               (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (m (f mphi2)) 
                                                  (r (N 2))) O))) O))) O) 0).


simpl in H0;
repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0);
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (to (f mphi1)) (i 2))) in H0;
simpl in H0.
rewrite H0.
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (reveal (f mphi2)) (i 2))) in H1; simpl in H1;  rewrite H1      . clear H1.
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (EQ_M (to (f mphi2)) (i 2))
                                                  FAlse)) in H1; simpl in H1;  rewrite H1      .
clear H1  .
(*********************)

pose proof(IFMORPH_B2 0   (EQ_M (to (f mphi2)) (i 2)) FAlse
                                       (if_then_else_B
                                          (EQ_M (act (f mphi2)) new) FAlse
                                          TRue) FAlse
                                   );
simpl in H1; rewrite IFFALSE_B in H1; repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1);
apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (reveal (f mphi3)) (i 2))) in H1;
simpl in H1;rewrite H1      ;clear H1.

(**********************)

pose proof(IFMORPH_B2 0   (if_then_else_B
                                          (EQ_M (to (f mphi2)) (i 2))
                                          (if_then_else_B
                                             (EQ_M (act (f mphi2)) new) FAlse
                                             TRue) FAlse) FAlse
                                    (EQ_M (act (f mphi1)) new) FAlse)
                                   ;
simpl in H1; rewrite IFFALSE_B in H1; repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1);
apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (reveal (f mphi3)) (i 2))) in H1;
simpl in H1;rewrite H1      ;clear H1.


(**********************************)

                pose proof(IFMORPH_B2 0             
                                     
                                          (if_then_else_B
                                             (EQ_M (act (f mphi2)) new) FAlse
                                             TRue) FAlse
                                       (EQ_M (act (f mphi1)) new) FAlse);


simpl in H1; rewrite IFFALSE_B in H1; repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1);
apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (to (f mphi2)) (i 2))) in H1;
simpl in H1;rewrite H1     . clear H1.


 pose proof(IFMORPH_B2 0  FAlse  TRue (EQ_M (act (f mphi1)) new) FAlse);




simpl in H1; rewrite IFFALSE_B in H1; repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1);
apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (act (f mphi2)) new)) in H1;
simpl in H1;rewrite H1     . clear H1.

clear H0.

(*************(EQ_M (reveal (f mphi3)) (i 1))
                                         (EQ_M (to (f mphi0)) (i 1))********)

pose proof(mor_eval_andB 1 (exp (pi1 (ggen (N 0))) 
                                         (m (f mphi0)) 
                                         (r (N 1)))
                                         (if_then_else_M
                                         (if_then_else_B
                                           (Bvar 1)
                                            (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                         (exp (pi1 (ggen (N 0)))
                                            (m (f mphi1)) 
                                            (r (N 2)))
                                         (if_then_else_M
                                            (if_then_else_B
                                               (EQ_M (reveal (f mphi3)) (i 2))
                                               (if_then_else_B
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi0)) new))
                                               FAlse)
                                            (exp (pi1 (ggen (N 0)))
                                               (m (f mphi1)) 
                                               (r (N 1)))
                                            (if_then_else_M
                                               (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (to (f mphi2)) (i 2))
                                                  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi1)) new))
                                                  FAlse) FAlse)
                                               (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (m (f mphi2)) 
                                                  (r (N 2))) O))) ).

simpl in H0.
 repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

apply Forall_ELM_EVAL_M with (n:=1) (x:= (EQ_M (reveal (f mphi3)) (i 1)) ) in H0;
apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (to (f mphi0)) (i 1))) in H0;
simpl in H0; rewrite H0     ; clear H0.


(*******************)

pose proof(IFMORPH_B1 FAlse TRue
                                   FAlse 0 1 );
simpl in H0;
 repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

apply Forall_ELM_EVAL_B with (n:=0) (b:=(EQ_M (act (f mphi1)) new)  ) in H0; simpl in H0;

apply Forall_ELM_EVAL_B with (n:=1) (b:=(EQ_M (reveal (f mphi2)) (i 2))  ) in H0;simpl in H0.
rewrite H0     . clear H0.


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (reveal (f mphi2)) (i 2))) in H0; simpl in H0;  rewrite H0.
clear H0  .
(*****************************)
pose proof(IFMORPH_B1  (if_then_else_B
                                                  (EQ_M (act (f mphi2)) new)
                                                  FAlse
                                                  (EQ_M (act (f mphi1)) new))
                                                  FAlse FAlse 0 1).
simpl in H0;
 repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

apply Forall_ELM_EVAL_B with (n:=0) (b:= (EQ_M (to (f mphi2)) (i 2))  ) in H0; simpl in H0;

apply Forall_ELM_EVAL_B with (n:=1) (b:=(EQ_M (reveal (f mphi3)) (i 2))  ) in H0;simpl in H0.
rewrite H0     . clear H0.




pose proof(IFMORPH_B1   FAlse
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse 0 1).
simpl in H0;
 repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

apply Forall_ELM_EVAL_B with (n:=0) (b:= (EQ_M (act (f mphi2)) new)  ) in H0; simpl in H0;

apply Forall_ELM_EVAL_B with (n:=1) (b:= (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2)) ) in H0;simpl in H0.
rewrite H0     . clear H0.




pose proof(IFMORPH_B1   FAlse
                                                  (if_then_else_B
                                                  (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2))
                                                  (EQ_M (act (f mphi1)) new)
                                                  FAlse) FAlse 0 1).
simpl in H0;
 repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

apply Forall_ELM_EVAL_B with (n:=0) (b:=  (EQ_M (act (f mphi2)) new)  ) in H0; simpl in H0;

apply Forall_ELM_EVAL_B with (n:=1) (b:= (EQ_M (to (f mphi2)) (i 2)) ) in H0;simpl in H0.
rewrite H0     . clear H0.


pose proof(IFMORPH_B1   (EQ_M (act (f mphi1)) new)
                                                  FAlse FAlse 0 1).
simpl in H0;
 repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

apply Forall_ELM_EVAL_B with (n:=0) (b:=   (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2)) ) in H0; simpl in H0;

apply Forall_ELM_EVAL_B with (n:=1) (b:=   (EQ_M (to (f mphi2)) (i 2)) ) in H0;simpl in H0.
rewrite H0     . clear H0.


pose proof(IFMORPH_B1   (EQ_M (act (f mphi1)) new)
                                                  FAlse FAlse 0 1).
simpl in H0;
 repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

apply Forall_ELM_EVAL_B with (n:=1) (b:=   (EQ_M 
                                                  (reveal (f mphi3)) 
                                                  (i 2)) ) in H0; simpl in H0;

apply Forall_ELM_EVAL_B with (n:=0) (b:=   (EQ_M (to (f mphi2)) (i 2)) ) in H0;simpl in H0.
rewrite H0     . clear H0.


pose proof(IFMORPH_B1   FAlse
                                               (EQ_M (act (f mphi0)) new)
                                            FAlse 0 1).
simpl in H0;
 repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

apply Forall_ELM_EVAL_B with (n:=1) (b:=    (EQ_M (reveal (f mphi3)) (i 2)) ) in H0; simpl in H0;

apply Forall_ELM_EVAL_B with (n:=0) (b:=    (EQ_M (act (f mphi1)) new) ) in H0;simpl in H0.
rewrite H0     . clear H0.



(************************

pose proof ( IFMORPH_M2 0  (if_then_else_B
                                       (EQ_M (to (f mphi2)) (i 2))
                                       (if_then_else_B
                                          (EQ_M (act (f mphi2)) new) FAlse
                                          (EQ_M (act (f mphi1)) new)) FAlse)
                                    FAlse
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi2)) (r (N 2))) O) ; simpl in H .
 repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
apply Forall_ELM_EVAL_M with (n:=0) (x:=(EQ_M (reveal (f mphi3)) (i 2)) ) in H1.
simpl in H1;rewrite H1 in H0;clear H1.

pose proof ( IFMORPH_M2 0   (if_then_else_B
                                          (EQ_M (act (f mphi2)) new) FAlse
                                          (EQ_M (act (f mphi1)) new)) FAlse
                                    (exp (pi1 (ggen (N 0))) 
                                       (m (f mphi2)) 
                                       (r (N 2))) O) ; simpl in H1.
 repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
apply Forall_ELM_EVAL_M with (n:=0) (x:=(EQ_M (to (f mphi2)) (i 2))) in H1.
simpl in H1;rewrite H1 in H0;clear H1.


pose proof ( IFMORPH_M2 0    FAlse
                                          (EQ_M (act (f mphi1)) new)
                                       (exp (pi1 (ggen (N 0))) 
                                          (m (f mphi2)) 
                                          (r (N 2))) O) ; simpl in H1.
 repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (act (f mphi2)) new)) in H1.
simpl in H1;rewrite H1 in H0;clear H1.


pose proof ( IFMORPH_M2 0   (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)   FAlse 

 (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                     (if_then_else_M (EQ_M (to (f mphi3)) (i 1))
                        (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r (N 4)))
                        O))  (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                     (if_then_else_M
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                        (if_then_else_M
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi1)) (i 1)) FAlse)
                           (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 2)))
                           (if_then_else_M
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
                                 (if_then_else_B (EQ_M (act (f mphi1)) new)
                                    FAlse (EQ_M (act (f mphi0)) new)) FAlse)
                              (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 1)))
                              (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
                                 (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
                                    (if_then_else_M
                                       (EQ_M (act (f mphi2)) new) O
                                       (if_then_else_M
                                          (EQ_M (act (f mphi1)) new)
                                          (exp (pi1 (ggen (N 0)))
                                             (m (f mphi2)) 
                                             (r (N 2))) O)) O) O)))) O) );
simpl in H1.
 repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (reveal (f mphi2)) (i 2))) in H1.
simpl in H1;rewrite H1 in H0;clear H1.
pose proof ( IFMORPH_M2 0     FAlse TRue  (if_then_else_M (EQ_M (reveal (f mphi3)) (i 1)) O
                        (if_then_else_M (EQ_M (to (f mphi3)) (i 1))
                           (exp (pi1 (ggen (N 0))) 
                              (pi2 (ggen (N 0))) (r (N 4))) O))  (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                        (if_then_else_M
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi0)) (i 1)) FAlse)
                           (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                           (if_then_else_M
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                 (EQ_M (to (f mphi1)) (i 1)) FAlse)
                              (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 2)))
                              (if_then_else_M
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 2))
                                    (if_then_else_B
                                       (EQ_M (act (f mphi1)) new) FAlse
                                       (EQ_M (act (f mphi0)) new)) FAlse)
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi1)) (r (N 1)))
                                 (if_then_else_M
                                    (EQ_M (reveal (f mphi3)) (i 2))
                                    (if_then_else_M
                                       (EQ_M (to (f mphi2)) (i 2))
                                       (if_then_else_M
                                          (EQ_M (act (f mphi2)) new) O
                                          (if_then_else_M
                                             (EQ_M (act (f mphi1)) new)
                                             (exp (pi1 (ggen (N 0)))
                                                (m (f mphi2)) 
                                                (r (N 2))) O)) O) O)))) O))
                     ; simpl in H1.
 repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (act (f mphi1)) new)) in H1.
simpl in H1;rewrite H1 in H0;clear H1.

pose proof ( IFMORPH_M2 0   (EQ_M (to (f mphi0)) (i 1)) FAlse  (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                           (if_then_else_M
                              (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                                 (EQ_M (to (f mphi1)) (i 1)) FAlse)
                              (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 2)))
                              (if_then_else_M
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi3)) (i 2))
                                    (if_then_else_B
                                       (EQ_M (act (f mphi1)) new) FAlse
                                       (EQ_M (act (f mphi0)) new)) FAlse)
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi1)) (r (N 1)))
                                 (if_then_else_M
                                    (EQ_M (reveal (f mphi3)) (i 2))
                                    (if_then_else_M
                                       (EQ_M (to (f mphi2)) (i 2))
                                       (if_then_else_M
                                          (EQ_M (act (f mphi2)) new) O
                                          (if_then_else_M
                                             (EQ_M (act (f mphi1)) new)
                                             (exp (pi1 (ggen (N 0)))
                                                (m (f mphi2)) 
                                                (r (N 2))) O)) O) O))) ) ; simpl in H1.
 repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (reveal (f mphi3)) (i 1))) in H1.
simpl in H1;rewrite H1 in H0;clear H1.

pose proof ( IFMORPH_M2 0    (EQ_M (to (f mphi1)) (i 1)) FAlse
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi1)) (r (N 2)))

 (if_then_else_M
                                    (if_then_else_B
                                       (EQ_M (reveal (f mphi3)) (i 2))
                                       (if_then_else_B
                                          (EQ_M (act (f mphi1)) new) FAlse
                                          (EQ_M (act (f mphi0)) new)) FAlse)
                                    (exp (pi1 (ggen (N 0))) 
                                       (m (f mphi1)) 
                                       (r (N 1)))
                                    (if_then_else_M
                                       (EQ_M (reveal (f mphi3)) (i 2))
                                       (if_then_else_M
                                          (EQ_M (to (f mphi2)) (i 2))
                                          (if_then_else_M
                                             (EQ_M (act (f mphi2)) new) O
                                             (if_then_else_M
                                                (EQ_M (act (f mphi1)) new)
                                                (exp 
                                                  (pi1 (ggen (N 0)))
                                                  (m (f mphi2)) 
                                                  (r (N 2))) O)) O) O)) ) ; simpl in H1.
 repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (reveal (f mphi3)) (i 1))) in H1.
simpl in H1;rewrite H1 in H0;clear H1. *)

