Load "tact_DH_3_irr".









Theorem Pi1_Pi2'': phi4 #### phi34.
Proof.
  repeat unf_phi. 
  
 
assert(H: (ostomsg t15) # (ostomsg t35)). 
   
simpl.
  
 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.

 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
 apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb.
 apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb. reflexivity.
simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.   repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb.


 Focus 2.   reflexivity. Focus 2. reflexivity.


 unfold mx2rn2, mx3rn1.
 (*********************************************************)

rewrite andB_assoc with (b1:= (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                          (EQ_M (to (f mphi1)) (i 1)) FAlse)
                       (EQ_M (to (f mphi0)) (i 3)) FAlse)
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)) (b2:=  (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b3:=   (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))) .
rewrite andB_comm with (b1 := (EQ_M (m x2) (grn 1))) (b2:= (EQ_M (m x3) (grn 2))).
rewrite  <- andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
rewrite <- andB_comm with (b1:= (EQ_M (m x2) (grn 1))). 
rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl.

(***************************************************************************)
rewrite andB_comm with (b1 :=  (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B (EQ_M (reveal (f mphi3)) (i 3))
                             (EQ_M (to (f mphi1)) (i 1)) FAlse)
                          (EQ_M (to (f mphi0)) (i 3)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                 (EQ_M (m (f mphi1))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                 FAlse)) (b2:=  (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))) .
simpl.
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))) .
simpl.
rewrite <- commexp with  (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0))))(x:= (rr (N 1))) (y:= (rr (N 2))).
(*********************************************************************************)
rewrite <- andB_assoc with (b1:= (EQ_M (m x2) (grn 1))) (b2:=  (if_then_else_B
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                     (EQ_M (to (f mphi1)) (i 1)) FAlse)
                  (EQ_M (to (f mphi0)) (i 3)) FAlse)
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) FAlse)
            (EQ_M (act (f mphi0)) new) FAlse)) (b3:= (EQ_M (m x3) (grn 2))).
rewrite andB_comm with (b1:= (EQ_M (m x2) (grn 1))) (b2:=  (if_then_else_B
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                     (EQ_M (to (f mphi1)) (i 1)) FAlse)
                  (EQ_M (to (f mphi0)) (i 3)) FAlse)
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) FAlse)
            (EQ_M (act (f mphi0)) new) FAlse)).
           
rewrite <- andB_assoc with (b1:=  (EQ_M (m x3) (grn 2))) (b2:=  
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B (EQ_M (reveal (f mphi3)) (i 3))
                          (EQ_M (to (f mphi1)) (i 1)) FAlse)
                       (EQ_M (to (f mphi0)) (i 3)) FAlse)
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)) (b3:=  (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_comm with (b1:= (EQ_M (m x3) (grn 2))) (b2:=   (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 3))
                        (EQ_M (to (f mphi1)) (i 1)) FAlse)
                     (EQ_M (to (f mphi0)) (i 3)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)). 
rewrite andB_assoc with (b1:= (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 3))
                        (EQ_M (to (f mphi1)) (i 1)) FAlse)
                     (EQ_M (to (f mphi0)) (i 3)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse) ) (b2:= (EQ_M (m x3) (grn 2))) (b3:= (EQ_M (m x2) (grn 1))). 
(***************************************  (EQ_M (reveal x4) (i 1)) ****************************************) 

rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=   (EQ_M (to x2) (i 1))) (b3:= (EQ_M (to (f mphi0)) (i 3))).

rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:= ((EQ_M (to x2) (i 1)) & (EQ_M (to (f mphi0)) (i 3)))) (b3:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).
rewrite andB_assoc with (b1:=  (EQ_M (reveal x4) (i 1))) (b2:=   (((EQ_M (to x2) (i 1)) & (EQ_M (to (f mphi0)) (i 3))) &
             (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:=   (EQ_M (act (f mphi0)) new)).
rewrite andB_assoc with ( b1 := (EQ_M (reveal x4) (i 1))) (b2:= ((((EQ_M (to x2) (i 1)) & (EQ_M (to (f mphi0)) (i 3))) &
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
           (EQ_M (act (f mphi0)) new))) (b3:=  (EQ_M (m x2) (grn 1))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=  (((((EQ_M (to x2) (i 1)) & (EQ_M (to (f mphi0)) (i 3))) &
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
            (EQ_M (act (f mphi0)) new)) & (EQ_M (m x2) (grn 1)))) (b3:= (EQ_M (m x3) (grn 2))).  (************************************ (EQ_M (reveal x4) (i 3)) *******************)
rewrite <- andB_comm with (b1:= (EQ_M (m x2) (grn 1))) (b2:= (EQ_M (m x3) (grn 2))) .
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 3))) (b2:=  (EQ_M (to (f mphi1)) (i 1))) (b3:= (EQ_M (to (f mphi0)) (i 3))).

rewrite andB_assoc with (b1:=  (EQ_M (reveal x4) (i 3))) (b2:=  ((EQ_M (to (f mphi1)) (i 1)) & (EQ_M (to (f mphi0)) (i 3)))) (b3:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).

rewrite andB_assoc with (b1:=  (EQ_M (reveal x4) (i 3)) ) (b2:= (((EQ_M (to (f mphi1)) (i 1)) & (EQ_M (to (f mphi0)) (i 3))) &
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:= (EQ_M (act (f mphi0)) new)).
rewrite  andB_assoc with (b1:= (EQ_M (reveal x4) (i 3))) (b2:= ((((EQ_M (to (f mphi1)) (i 1)) & (EQ_M (to (f mphi0)) (i 3))) &
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
             (EQ_M (act (f mphi0)) new))) (b3:=  ((EQ_M (m x2) (grn 1)) & (EQ_M (m x3) (grn 2)))).
rewrite <- andB_assoc with (b1:= ((((EQ_M (to (f mphi1)) (i 1)) & (EQ_M (to (f mphi0)) (i 3))) &
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
             (EQ_M (act (f mphi0)) new))) (b2:= (EQ_M (m x2) (grn 1))) (b3:= (EQ_M (m x3) (grn 2))).
(**********************************************************************************)
 rewrite andB_elm' with (b1:=   (EQ_M (reveal x4) (i 1))) (b2:=    ((((((EQ_M (to x2) (i 1)) & (EQ_M (to (f mphi0)) (i 3))) &
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
           (EQ_M (act (f mphi0)) new)) & (EQ_M (m x2) (grn 1))) &
         (EQ_M (m x3) (grn 2)))).

rewrite IFEVAL_M' with (b:= (((((EQ_M (to x2) (i 1)) & (EQ_M (to (f mphi0)) (i 3))) &
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
             (EQ_M (act (f mphi0)) new)) & (EQ_M (m x2) (grn 1))) &
           (EQ_M (m x3) (grn 2))).
simpl. repeat redg. repeat rewrite IFTFb.

rewrite <- IFSAME_M with (b:= (EQ_M (reveal x4) (i 1))) at 1.
apply breq_msgeq'  .    repeat redg. simpl. repeat rewrite  IFTFb.
simpl.
 
repeat redg. 


 
(**********************************************(EQ_M (to (f mphi1)) (i 1))**********)

rewrite andB_assoc with (b1:= (EQ_M (to (f mphi1)) (i 1))) (b2:= (EQ_M (to (f mphi0)) (i 3))) (b3:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi1)) (i 1))) (b2:=((EQ_M (to (f mphi0)) (i 3)) &
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:= (EQ_M (act (f mphi0)) new)).

rewrite andB_assoc with (b1:= (EQ_M (to (f mphi1)) (i 1))) (b2:=  (((EQ_M (to (f mphi0)) (i 3)) &
                (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
               (EQ_M (act (f mphi0)) new))) (b3:=  (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_assoc with (b1:=  (EQ_M (to (f mphi1)) (i 1))) (b2:=  ((((EQ_M (to (f mphi0)) (i 3)) &
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
             (EQ_M (act (f mphi0)) new)) &
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))) (b3:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:=  (EQ_M (to (f mphi1)) (i 1))) (b2:=  (((((EQ_M (to (f mphi0)) (i 3)) &
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
           (EQ_M (act (f mphi0)) new)) &
          (EQ_M (m (f mphi1))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
(**************************************************************************)
apply breq_msgeq'.  simpl.   repeat redg. 

rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 3))) (b2:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b3:= (EQ_M (act (f mphi0)) new)).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 3))) (b2:=  ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
               (EQ_M (act (f mphi0)) new))) (b3:=  (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).

rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 3)))  (b2:=   (((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
             (EQ_M (act (f mphi0)) new)) &
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))) (b3:=   (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:= (EQ_M (to (f mphi0)) (i 3))) (b2:=  ((((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
           (EQ_M (act (f mphi0)) new)) &
          (EQ_M (m (f mphi1))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).

repeat rewrite IFTFb.
rewrite <- IFSAME_M with (b:=  (EQ_M (to (f mphi0)) (i 3))) at 1.
apply breq_msgeq'.  simpl.
repeat redg.
repeat rewrite IFTFb.
rewrite andB_comm with (b1:= (if_then_else_B
                 (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                 (EQ_M (act (f mphi0)) new) FAlse)) (b2:=   (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_assoc with (b1:=  (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:=   (if_then_else_B
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
              (EQ_M (act (f mphi0)) new) FAlse)) (b3:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite <-  IFSAME_M with (b:=  (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))) &
        ((if_then_else_B
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
            (EQ_M (act (f mphi0)) new) FAlse) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))) at 1.

repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) . simpl. 
reflexivity. reflexivity. simpl. redg. reflexivity.  
simpl. repeat redg.
rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 3))) (b2:=  (if_then_else_B
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
                          (EQ_M (to (f mphi0)) (i 3)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                 (EQ_M (m (f mphi1))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
                 FAlse)
              (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
              FAlse)).

rewrite andB_assoc with (b1:= (EQ_M (reveal (f mphi3)) (i 3)) ) (b2:=  (EQ_M (to (f mphi0)) (i 3)))
(b3:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).
rewrite andB_assoc with (b1:= (EQ_M (reveal (f mphi3)) (i 3))) (b2:=  ((EQ_M (to (f mphi0)) (i 3)) &
          (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:= (EQ_M (act (f mphi0)) new)).
rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 3))) (b2:=   (((EQ_M (to (f mphi0)) (i 3)) &
        (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
       (EQ_M (act (f mphi0)) new))).
apply breq_msgeq'.  simpl.
repeat redg.
rewrite andB_comm with (b1:= (EQ_M (to (f mphi1)) (i 1))) (b2:=  (EQ_M (to (f mphi0)) (i 3))).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 3))) (b2:= (EQ_M (to (f mphi1)) (i 1))) (b3:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 3))) (b2:=   ((EQ_M (to (f mphi1)) (i 1)) &
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:=  (EQ_M (act (f mphi0)) new)).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 3))) (b2:=  (((EQ_M (to (f mphi1)) (i 1)) &
                (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
               (EQ_M (act (f mphi0)) new))) (b3:=  (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_assoc with (b1:=  (EQ_M (to (f mphi0)) (i 3))) (b2:=    ((((EQ_M (to (f mphi1)) (i 1)) &
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
             (EQ_M (act (f mphi0)) new)) &
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))) (b3:=   (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:=   (EQ_M (to (f mphi0)) (i 3))) (b2:=  (((((EQ_M (to (f mphi1)) (i 1)) &
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
           (EQ_M (act (f mphi0)) new)) &
          (EQ_M (m (f mphi1))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 3))) (b2:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b3:= (EQ_M (act (f mphi0)) new)).
rewrite andB_elm' with (b1:= (EQ_M (to (f mphi0)) (i 3))) (b2:= ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
       (EQ_M (act (f mphi0)) new))).
apply breq_msgeq'.  simpl. repeat redg.
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi1)) (i 1))) (b2:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b3:= (EQ_M (act (f mphi0)) new)).
rewrite andB_comm with (b1:=  (EQ_M (to (f mphi1)) (i 1))) (b2:= ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
               (EQ_M (act (f mphi0)) new))).
rewrite andB_assoc with (b1:=   ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
               (EQ_M (act (f mphi0)) new))) (b2:= (EQ_M (to (f mphi1)) (i 1))) (b3:=  (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_assoc with (b1:=  ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
            (EQ_M (act (f mphi0)) new))) (b2:=  ((EQ_M (to (f mphi1)) (i 1)) &
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))) (b3:=    (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))). 
rewrite andB_elm' with (b1:= ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
         (EQ_M (act (f mphi0)) new))) (b2:=   (((EQ_M (to (f mphi1)) (i 1)) &
          (EQ_M (m (f mphi1))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
apply breq_msgeq'.  simpl. repeat redg.
rewrite <- IFSAME_M with (b:=   (if_then_else_B
           (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
              (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
              FAlse)
           (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))) FAlse)) at 1.
rewrite andB_comm with (b1:=  (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))) FAlse)) (b2:= (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))) . simpl. rewrite commexp.   reflexivity. 
(********************************************************)
simpl.  repeat redg.
reflexivity. 
simpl. repeat redg. reflexivity. 
simpl.  repeat redg. reflexivity. 
simpl. repeat redg. 
apply breq_msgeq'  .    repeat redg. simpl. repeat rewrite  IFTFb.
apply breq_msgeq'  .    repeat redg. simpl. repeat rewrite  IFTFb. reflexivity. 
simpl. reflexivity. 
simpl.  repeat redg. repeat rewrite  IFTFb.
apply breq_msgeq'  .    repeat redg. simpl. repeat rewrite  IFTFb. 
simpl. 
apply breq_msgeq'  .   reflexivity.   Focus 2. reflexivity. repeat redg. simpl. repeat rewrite  IFTFb. apply breq_msgeq'  .   reflexivity.
simpl. 
apply breq_msgeq'  . repeat redg. simpl. reflexivity. 
simpl. 
apply breq_msgeq'  . repeat redg. simpl.
apply breq_msgeq'  . repeat redg. simpl. reflexivity. simpl. 
repeat rewrite  IFTFb. repeat redg.
apply breq_msgeq'. reflexivity. 
simpl.  apply breq_msgeq'  .  reflexivity. repeat redg. simpl.
 apply breq_msgeq'  .  reflexivity. repeat redg. simpl.
repeat redg.  repeat rewrite  IFTFb.
 apply breq_msgeq'  .  simpl. Focus 2. reflexivity. repeat rewrite  IFTFb. 
rewrite andB_assoc with (b1:=  (EQ_M (reveal (f mphi3)) (i 1))) (b2:= (EQ_M (to (f mphi0)) (i 3))) (b3:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) .
repeat redg. simpl.
rewrite  andB_assoc with (b1 := (EQ_M (reveal (f mphi3)) (i 1))) (b2 :=     ((EQ_M (to (f mphi0)) (i 3)) &
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:= (EQ_M (act (f mphi0)) new)).
rewrite andB_assoc with (b1:= (EQ_M (reveal (f mphi3)) (i 1))) (b2:=   (((EQ_M (to (f mphi0)) (i 3)) &
                (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
               (EQ_M (act (f mphi0)) new))) (b3:= (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_assoc with (b1:=  (EQ_M (reveal (f mphi3)) (i 1))) (b2:=  ((((EQ_M (to (f mphi0)) (i 3)) &
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
             (EQ_M (act (f mphi0)) new)) &
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))) (b3:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:=  (EQ_M (reveal (f mphi3)) (i 1))) (b2:=  (((((EQ_M (to (f mphi0)) (i 3)) &
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
           (EQ_M (act (f mphi0)) new)) &
          (EQ_M (m (f mphi1))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
 apply breq_msgeq'  .  simpl. Focus 2. reflexivity. repeat rewrite  IFTFb. 
rewrite andB_assoc with (b1:=  (EQ_M (to (f mphi0)) (i 3))) (b2:=  ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
               (EQ_M (act (f mphi0)) new))) (b3:= (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_assoc with (b1:=  (EQ_M (to (f mphi0)) (i 3))) (b2:= (((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
             (EQ_M (act (f mphi0)) new)) &
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))) (b3:= (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:= (EQ_M (to (f mphi0)) (i 3))) (b2:= ((((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
           (EQ_M (act (f mphi0)) new)) &
          (EQ_M (m (f mphi1))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))). 
rewrite <- IFSAME_M with (b:= (EQ_M (to (f mphi0)) (i 3))) at 1.
apply breq_msgeq'.  simpl.
Focus 2. reflexivity. Focus 2. reflexivity.
 Focus 2.
simpl. 
repeat redg.
 (b3:=   (exp (pi1 (ggen (N 0)))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))) 
           (rr (N 2)))).
  repeat redg. repeat rewrite IFTFb.
rewrite IFEVAL_M' with (b:= 
rewrite <- IFSAME_M with (b:=  (if_then_else_B
           (if_then_else_B
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
                       (EQ_M (to (f mphi0)) (i 3)) FAlse)
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)
              (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
              FAlse)
           (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))) FAlse)) at 1.
 reflexivity. 
assert(x4 # O).
simpl. unfold x4.
rewrite H4. simpl. 
assert( H5: check_eq_msg (reveal (f mphi3)) (reveal (f mphi3)) =  true).
simpl.
unfold check_eq_msg. simpl.

  simpl.  repeat redg. repeat rewrite IFTFb. reflexivity.
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=   ((EQ_M (to x3) (i 1)) &
                                         (EQ_M (to x2) (i 2)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=    (((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=    ((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x3) new)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=    (((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x3) new))) &
                                                                         (EQ_M (act x1) new))). 

rewrite <- andB_assoc with (b2:= (EQ_M (reveal x4) (i 2))).
rewrite  andB_comm with (b2:= (EQ_M (reveal x4) (i 2))).
rewrite andB_assoc with  (b1:= (EQ_M (reveal x4) (i 2))).

(************************************************************************)

rewrite andB_comm with (b1 := (((((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                 (EQ_M (to x2) (i 2))) &
                                                (EQ_M (to x1) (i 1))) &
                                               (notb (EQ_M (act x3) new))) &
                                              (EQ_M (act x1) new)) &
                                                                   (EQ_M (m x2) (grn 1)))) .

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))) .
simpl.
 apply breq_msgeq1'. simpl.
apply breq_msgeq1'. simpl. repeat redg.
apply breq_msgeq1'. simpl. repeat redg.
apply breq_msgeq'.  simpl.
rewrite IFTFb.
apply breq_msgeq'.   simpl.  reflexivity. 
apply breq_msgeq'. reflexivity.
apply breq_msgeq'.
  simpl.
apply breq_msgeq1'. simpl. repeat redg.
apply breq_msgeq1'. simpl. repeat redg.

reflexivity. 
simpl. repeat redg.

apply breq_msgeq1'. simpl. repeat redg.
apply breq_msgeq1'. simpl. repeat redg.
repeat rewrite IFTFb.
apply breq_msgeq1'. simpl. repeat redg.

repeat rewrite IFTFb.
apply breq_msgeq1'. simpl. repeat redg.

repeat aply_breq_then_same.
assert(H1: qa100_ss # qb100_ss).
unfold qa100_ss, qb100_ss.
assert(H2: qa101_s # qb101_s).
unfold qa101_s, qb101_s.
assert(H3: qa102 # qb102).
unfold qa102, qb102.
apply breq_msgeq1'. unfold subbol_msg'. simpl. repeat redg.
 
repeat aply_breq_then_same.
repeat aply_breq.
 repeat unf.
 unfold mx2rn2, mx3rn1.
 

rewrite andB_assoc with (b2:=  (EQ_M (m x2) (grn 1))) .
rewrite andB_comm with (b1 := (EQ_M (m x2) (grn 1))) (b2:= (EQ_M (m x3) (grn 2))).
rewrite  <- andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
rewrite <- andB_comm with (b1:= (EQ_M (m x2) (grn 1))). 
rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl.

rewrite andB_comm with (b1 := (((((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x3) (i 1))) &
                                                 (EQ_M (to x2) (i 2))) &
                                                (EQ_M (to x1) (i 1))) &
                                               (notb (EQ_M (act x3) new))) &
                                              (EQ_M (act x1) new)) &
                                                                   (EQ_M (m x2) (grn 1)))) .

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))) .
simpl.




rewrite <- commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (y:= (rr (N 2))) (x:= (rr (N 1))).
(**********************************(EQ_M (reveal x4) (i 2))***********************************************) 
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=   (EQ_M (to x3) (i 1))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=   ((EQ_M (to x3) (i 1)) &
                                         (EQ_M (to x2) (i 2)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=    (((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=    ((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x3) new)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 2))) (b2:=    (((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x3) new))) &
                                                                         (EQ_M (act x1) new))). 

rewrite <- andB_assoc with (b2:= (EQ_M (reveal x4) (i 2))).
rewrite  andB_comm with (b2:= (EQ_M (reveal x4) (i 2))).
rewrite andB_assoc with  (b1:= (EQ_M (reveal x4) (i 2))).




(******************(EQ_M (reveal x4) (i 1)) *************************)
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b3:=   (EQ_M (to x2) (i 2))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=   ((EQ_M (to x3) (i 1)) &
                                         (EQ_M (to x2) (i 2)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=    (((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=    ((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x3) new)))).
rewrite andB_assoc with (b1:= (EQ_M (reveal x4) (i 1))) (b2:=    (((((EQ_M (to x3) (i 1)) &
                                               (EQ_M (to x2) (i 2))) &
                                              (EQ_M (to x1) (i 1))) &
                                             (notb (EQ_M (act x3) new))) &
                                                                         (EQ_M (act x1) new))). 

rewrite <- andB_assoc with (b2:= (EQ_M (reveal x4) (i 1))).
rewrite  andB_comm with (b2:= (EQ_M (reveal x4) (i 1))).
rewrite andB_assoc with  (b2:= (EQ_M (m x3) (grn 2))).



(********************************************************************)

rewrite <- andB_assoc with (b1:= (EQ_M (m x3) (grn 2))) (b3:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b2:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b1:= (EQ_M (m x3) (grn 2))).

(**********************************************************************)

repeat aply_breq_then_same.

aply_breq. 
repeat aply_breq_then_same.
aply_breq.
repeat aply_breq_then_same.
aply_breq.
repeat rewrite IFTFb.
repeat redg.

rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:=   (if_then_else_B
              (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B (EQ_M (to (f mphi2)) (i 1))
                             (EQ_M (to (f mphi1)) (i 2)) FAlse)
                          (EQ_M (to (f mphi0)) (i 1)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                 (EQ_M (m (f mphi2))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
                 FAlse) FAlse) ).
 
rewrite <- IFSAME_M with (b:= (EQ_M (reveal (f mphi3)) (i 2))).

apply breq_msgeq'. 
unfold subbol_msg'.  
unfold check_eq_msg.
unfold check_eq_listm.
unfold beq_nat.
 unfold andb.
repeat redg.

simpl.




rewrite IFEVAL_M' with (b:=   (if_then_else_B
           (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
           (if_then_else_B
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B (EQ_M (to (f mphi2)) (i 1))
                          (EQ_M (to (f mphi1)) (i 2)) FAlse)
                       (EQ_M (to (f mphi0)) (i 1)) FAlse)
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)
              (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
              FAlse) FAlse)).
unfold subbol_msg'.  
unfold check_eq_msg.
unfold check_eq_listm.
unfold beq_nat.

repeat redg.
simpl.
repeat redg.
(*************************************************************)
rewrite andB_comm with (b1 :=   (EQ_M (to (f mphi2)) (i 1))) (b2:=   (EQ_M (to (f mphi1)) (i 2)))  .
rewrite  andB_assoc with (b1:=  (EQ_M (to (f mphi1)) (i 2))) (b2:=  (EQ_M (to (f mphi2)) (i 1))) (b3:= (EQ_M (to (f mphi0)) (i 1))).  
rewrite  andB_assoc with (b1:=  (EQ_M (to (f mphi1)) (i 2))) (b2:=   ((EQ_M (to (f mphi2)) (i 1)) &
                     (EQ_M (to (f mphi0)) (i 1))))
(b3:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))  .
rewrite  andB_assoc with (b1:=  (EQ_M (to (f mphi1)) (i 2))) (b2:=  (((EQ_M (to (f mphi2)) (i 1)) & (EQ_M (to (f mphi0)) (i 1))) &
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:=  (EQ_M (act (f mphi0)) new)).
rewrite  andB_assoc with (b1:=  (EQ_M (to (f mphi1)) (i 2))) (b2:=    ((((EQ_M (to (f mphi2)) (i 1)) & (EQ_M (to (f mphi0)) (i 1))) &
                (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
               (EQ_M (act (f mphi0)) new))) 
(b3:=   (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))  .
rewrite <- andB_assoc with (b1:=  (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:=  (EQ_M (to (f mphi1)) (i 2))) (b3:=   (((((EQ_M (to (f mphi2)) (i 1)) & (EQ_M (to (f mphi0)) (i 1))) &
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
             (EQ_M (act (f mphi0)) new)) &
            (EQ_M (m (f mphi2))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))) .
rewrite andB_comm with (b1:= (EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi1)) (i 2))).


(******************************************************************)


repeat rewrite andB_elm' with (b1:=  (EQ_M (to (f mphi1)) (i 2))) (b2:=   ((EQ_M (m (f mphi1))
          (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))) &
       (((((EQ_M (to (f mphi2)) (i 1)) & (EQ_M (to (f mphi0)) (i 1))) &
          (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
         (EQ_M (act (f mphi0)) new)) &
        (EQ_M (m (f mphi2))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))))).
rewrite <- IFSAME_M with (b:=  (EQ_M (to (f mphi1)) (i 2))).
aply_breq.


repeat rewrite andB_elm' with (b1:= (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:=  (if_then_else_B
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B (EQ_M (to (f mphi2)) (i 1))
                       (EQ_M (to (f mphi0)) (i 1)) FAlse)
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)
              (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
              FAlse)).

rewrite <- IFSAME_M with (b:=  (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).

Axiom EQbrmsg_msg'' :forall  ( m m1 m2 m3 m4 :message) ,  (if_then_else_M  (EQ_M m1 m2 )  (submsg_msg' m m1 m3) m4) #  (if_then_else_M (EQ_M m1 m2)   (submsg_msg' m m2 m3) m4).
pose proof ( EQbrmsg_msg''  (m (f mphi1))  (m (f mphi1))  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))  
         (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 2)))   
         (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 2)))).
simpl in H.
rewrite H.
 
aply_breq. repeat redg. 
assert( (subbol_msg' (EQ_M (reveal (f mphi3)) (i 2)) FAlse
      (if_then_else_M
         (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
            (EQ_M (to (f mphi1)) (i 2)) FAlse)
         (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 2)))
         (if_then_else_M
            (if_then_else_B (EQ_M (reveal (f mphi3)) (i 2))
               (EQ_M (to (f mphi0)) (i 2)) FAlse)
            (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 2)))
            (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
               (if_then_else_M
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O))))) #  (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi2)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
               (if_then_else_M
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O)) ).
simpl. repeat redg. reflexivity.
rewrite H. clear H.

simpl.

 repeat redg.
(************************************************************************)
 rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 1))) (b2:=   (if_then_else_B
              (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B
                          (if_then_else_B (EQ_M (to (f mphi2)) (i 1))
                             (EQ_M (to (f mphi1)) (i 2)) FAlse)
                          (EQ_M (to (f mphi0)) (i 1)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                 (EQ_M (m (f mphi2))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
                 FAlse) FAlse)). 
rewrite <- IFSAME_M with (b:=  (EQ_M (reveal (f mphi3)) (i 1))).
   apply breq_msgeq'.
repeat unfold subbol_msg'.
repeat unfold check_eq_msg.
repeat rewrite <- beq_nat_refl.
simpl.

repeat redg.

 rewrite andB_elm' with (b1:= (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:=    (if_then_else_B
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B (EQ_M (to (f mphi2)) (i 1))
                          (EQ_M (to (f mphi1)) (i 2)) FAlse)
                       (EQ_M (to (f mphi0)) (i 1)) FAlse)
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)
              (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
              FAlse)). 
rewrite <- IFSAME_M with (b:=   (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
aply_breq.

(********************RHS***********************)
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi2)) (i 1))) (b2:=  (EQ_M (to (f mphi1)) (i 2))) (b3:=   (EQ_M (to (f mphi0)) (i 1))).

rewrite andB_assoc with (b1:= (EQ_M (to (f mphi2)) (i 1))) (b2:=  ((EQ_M (to (f mphi1)) (i 2)) & (EQ_M (to (f mphi0)) (i 1))))  (b3:=   (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).

rewrite andB_assoc with (b1:= (EQ_M (to (f mphi2)) (i 1))) (b2:=  (((EQ_M (to (f mphi1)) (i 2)) & (EQ_M (to (f mphi0)) (i 1))) &
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)))  (b3:=  (EQ_M (act (f mphi0)) new)  ).

rewrite andB_assoc with (b1:=  (EQ_M (to (f mphi2)) (i 1))) (b2:=  ((((EQ_M (to (f mphi1)) (i 2)) & (EQ_M (to (f mphi0)) (i 1))) &
             (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
            (EQ_M (act (f mphi0)) new))) (b3:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
(******************************LHS***********************)

rewrite andB_assoc with (b1:= (EQ_M (to (f mphi2)) (i 1)))  (b2:=  (EQ_M (to (f mphi0)) (i 1))) (b3:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).

rewrite andB_assoc with ( b1:=   (EQ_M (to (f mphi2)) (i 1))) (b2:= ((EQ_M (to (f mphi0)) (i 1)) &
          (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)))  (b3:= (EQ_M (act (f mphi0)) new)).
(*****************************************)
rewrite andB_elm' with (b1:=  (EQ_M (to (f mphi2)) (i 1))) (b2:=  (((EQ_M (to (f mphi0)) (i 1)) &
        (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
       (EQ_M (act (f mphi0)) new))).

rewrite andB_elm' with (b1:= (EQ_M (to (f mphi2)) (i 1))) (b2:=  (((((EQ_M (to (f mphi1)) (i 2)) & (EQ_M (to (f mphi0)) (i 1))) &
           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
          (EQ_M (act (f mphi0)) new)) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
aply_breq.


(******************LHS************************)
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 1))) (b2:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) ) (b3:=  (EQ_M (act (f mphi0)) new)).

rewrite andB_elm' with (b1:=   (EQ_M (to (f mphi0)) (i 1))) (b2:=  ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
       (EQ_M (act (f mphi0)) new))).
(*****************RHS****************************)
rewrite andB_comm with (b1:=  (EQ_M (to (f mphi1)) (i 2))) (b2:=  (EQ_M (to (f mphi0)) (i 1))).
rewrite andB_assoc with (b1:=    (EQ_M (to (f mphi0)) (i 1))) (b2:=  (EQ_M (to (f mphi1)) (i 2))) (b3:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).

rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 1))) (b2:=    ((EQ_M (to (f mphi1)) (i 2)) &
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:=  (EQ_M (act (f mphi0)) new)).

rewrite andB_assoc with (b1:=  (EQ_M (to (f mphi0)) (i 1))) (b2:=   (((EQ_M (to (f mphi1)) (i 2)) &
             (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
            (EQ_M (act (f mphi0)) new))) (b3:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:=  (EQ_M (to (f mphi0)) (i 1))).

(***************************************************************)


aply_breq.

(****************LHS*************************)
rewrite andB_elm' with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:= (EQ_M (act (f mphi0)) new)).

(******************************RHS*****************)
rewrite andB_comm with (b1:= (EQ_M (to (f mphi1)) (i 2))) (b2:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).
rewrite andB_assoc with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:=  (EQ_M (to (f mphi1)) (i 2))) (b3:= (EQ_M (act (f mphi0)) new)).
rewrite andB_assoc with (b1:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:=  ((EQ_M (to (f mphi1)) (i 2)) & (EQ_M (act (f mphi0)) new))) (b3:= (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).


aply_breq.

rewrite andB_comm with (b1:=  (EQ_M (to (f mphi1)) (i 2))) (b2:= (EQ_M (act (f mphi0)) new)) .
rewrite andB_assoc with (b1:= (EQ_M (act (f mphi0)) new)) (b2:= (EQ_M (to (f mphi1)) (i 2))) (b3:= 
 (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:=   (EQ_M (act (f mphi0)) new)).
aply_breq.

rewrite andB_comm with (b1:= (EQ_M (to (f mphi1)) (i 2))) (b2:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:= (EQ_M (m (f mphi2))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))) (b2:=  (EQ_M (to (f mphi1)) (i 2))).

(**********************************************)
rewrite <- IFSAME_M with (b:=   (EQ_M (m (f mphi2))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).

pose proof (EQbrmsg_msg'' (m (f mphi2)) (m (f mphi2))  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))  (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))  (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1))) ).
simpl in H.

rewrite H. 
aply_breq. clear H.
 rewrite <- commexp with (x:=  (rr (N 1))).

rewrite  IFSAME_M . reflexivity.

(**************************subgoal 2************************************)
simpl.

repeat redg. reflexivity.

(**************************subgoal 3*************************************)
aply_breq.

aply_breq.

repeat rewrite IFTFb.
repeat redg.
aply_breq.

aply_breq_then_same.

aply_breq.

repeat rewrite IFTFb.
repeat redg.
(**********************RHS******************************************)

rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:=  (if_then_else_B
              (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B (EQ_M (to (f mphi0)) (i 1))
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                 (EQ_M (m (f mphi2))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))) 
                 FAlse) FAlse)).
apply breq_msgeq'.
simpl.
repeat rewrite IFTFb.
repeat redg.

rewrite andB_elm' with (b1:=  (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:=   (if_then_else_B
              (if_then_else_B
                 (if_then_else_B (EQ_M (to (f mphi0)) (i 1))
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)
              (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
              FAlse)).
(********************************LHS**********************************)
rewrite <-IFSAME_M with (b:=  (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
pose proof(EQbrmsg_msg'' (m (f mphi1)) (m (f mphi1))  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 2)))  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 2))) ).
simpl in H. 

rewrite H.

aply_breq. clear H.

rewrite IFSAME_M. reflexivity. clear H.
repeat redg. reflexivity.

(************************************subgoal*************************)
repeat rewrite IFTFb.
repeat redg.
simpl.
repeat redg.
rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 1))) (b2:=   (if_then_else_B
              (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B (EQ_M (to (f mphi0)) (i 1))
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                 (EQ_M (m (f mphi2))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
                 FAlse) FAlse)).
rewrite <- IFSAME_M with (b:= (EQ_M (reveal (f mphi3)) (i 1))).
aply_breq.

rewrite andB_elm' with (b1:=  (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2 :=  (if_then_else_B
              (if_then_else_B
                 (if_then_else_B (EQ_M (to (f mphi0)) (i 1))
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)
              (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
              FAlse)).

rewrite <- IFSAME_M with (b:= (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).

aply_breq.

rewrite andB_elm' with (b1:= (if_then_else_B
              (if_then_else_B (EQ_M (to (f mphi0)) (i 1))
                 (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) FAlse)
              (EQ_M (act (f mphi0)) new) FAlse)) (b2:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
aply_breq.

rewrite <- IFSAME_M with (b:= (EQ_M (m (f mphi2))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
pose proof(EQbrmsg_msg'' (m (f mphi2)) (m (f mphi2)) (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))  (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))  (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))).
simpl in H.
rewrite H.
aply_breq.
rewrite commexp. reflexivity.
 
(**************************subgoal 2***********************)
 aply_breq.
aply_breq.
aply_breq.
aply_breq.
aply_breq.
aply_breq.
aply_breq.
aply_breq.
repeat redg.
repeat rewrite IFTFb.
(***********************************LHS************************)

rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:= (EQ_M (to (f mphi1)) (i 2))).

repeat redg.
repeat rewrite IFTFb.

(*******************************RHS*****************************)

rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 2))) (b2:=   (if_then_else_B
              (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B (EQ_M (to (f mphi1)) (i 2))
                          (EQ_M (to (f mphi0)) (i 1)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                 (EQ_M (m (f mphi2))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
                  FAlse) FAlse)).
 apply breq_msgeq'.
(************************LHS****************************)
assert((subbol_msg' (EQ_M (reveal (f mphi3)) (i 2)) TRue
      (if_then_else_M (EQ_M (to (f mphi1)) (i 2))
         (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 2)))
         (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
            (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 2)))
            (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
               (if_then_else_M
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B
                           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                              (EQ_M (to (f mphi1)) (i 1)) FAlse)
                           (EQ_M (to (f mphi0)) (i 1)) FAlse)
                        (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                        FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O))))) #  (if_then_else_M (EQ_M (to (f mphi1)) (i 2))
      (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 2))) 
      (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 2))))).
unfold subbol_msg'.
assert(check_eq_msg (to (f mphi1)) (reveal (f mphi3)) = false).
simpl. reflexivity. 
assert(check_eq_msg (reveal (f mphi3)) (reveal (f mphi3)) = true).   unfold check_eq_msg. unfold check_eq_listm. unfold mphi3.  simpl.  reflexivity.
 assert (    check_eq_msg (i 2) (i 2) = true). simpl. reflexivity.
rewrite H, H0, H1. simpl.
 repeat redg.  reflexivity. 
rewrite H. clear H.  
(****************************RHS************************************************)

unfold subbol_msg'.
assert(check_eq_msg (reveal (f mphi3)) (reveal (f mphi3)) = true).   unfold check_eq_msg. unfold check_eq_listm. unfold mphi3.  simpl.  reflexivity.
 assert (    check_eq_msg (i 2) (i 2) = true). simpl. reflexivity.
rewrite H, H0.
clear .
simpl.
repeat redg.
repeat rewrite IFTFb.
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi1)) (i 2))) (b2:= (EQ_M (to (f mphi0)) (i 1))) (b3:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi1)) (i 2))) (b2:=  ((EQ_M (to (f mphi0)) (i 1)) &
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:=   (EQ_M (act (f mphi0)) new)).

rewrite andB_assoc with (b1:= (EQ_M (to (f mphi1)) (i 2))) (b2:=  (((EQ_M (to (f mphi0)) (i 1)) &
                (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
               (EQ_M (act (f mphi0)) new))) (b3:=   (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite <- andB_assoc with (b1:=  (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:=  (EQ_M (to (f mphi1)) (i 2))) (b3:=    ((((EQ_M (to (f mphi0)) (i 1)) &
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
             (EQ_M (act (f mphi0)) new)) &
            (EQ_M (m (f mphi2))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
rewrite andB_comm with (b1:= (EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:=
         (EQ_M (to (f mphi1)) (i 2))).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi1)) (i 2)) ) (b2:=  (EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b3:=   ((((EQ_M (to (f mphi0)) (i 1)) &
           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
          (EQ_M (act (f mphi0)) new)) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).

rewrite andB_elm' with (b1:= (EQ_M (to (f mphi1)) (i 2))  ) (b2:=    ((EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))) &
         ((((EQ_M (to (f mphi0)) (i 1)) &
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
           (EQ_M (act (f mphi0)) new)) &
          (EQ_M (m (f mphi2))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))))).
aply_breq.

rewrite IFEVAL_M'.
simpl.
repeat redg.

rewrite <- IFSAME_M with (b:=  (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).

pose proof(EQbrmsg_msg''  (m (f mphi1))  (m (f mphi1))  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 2)))  (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 2))) ). simpl in H. 
rewrite H. clear .
rewrite andB_elm' with (b1:= (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:=   (if_then_else_B
              (if_then_else_B
                 (if_then_else_B (EQ_M (to (f mphi0)) (i 1))
                    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                    FAlse) (EQ_M (act (f mphi0)) new) FAlse)
              (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
              FAlse)).
aply_breq.
repeat redg. reflexivity. 
(******************************subgoal******************) 
assert(  (subbol_msg' (EQ_M (reveal (f mphi3)) (i 2)) FAlse
      (if_then_else_M (EQ_M (reveal (f mphi3)) (i 2))
         (exp (pi1 (ggen (N 0))) (m (f mphi0)) (rr (N 2)))
         (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
            (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi1)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O)))) # (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
            (if_then_else_M
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B
                        (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                           (EQ_M (to (f mphi1)) (i 1)) FAlse)
                        (EQ_M (to (f mphi0)) (i 1)) FAlse)
                     (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                     FAlse) (EQ_M (act (f mphi0)) new) FAlse)
               (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O))).
simpl.
repeat redg. reflexivity.
rewrite H.  clear.
unfold subbol_msg'.
assert(check_eq_msg (reveal (f mphi3)) (reveal (f mphi3)) &&
                  check_eq_msg (i 2) (i 2) = true).
simpl. reflexivity.  rewrite H. repeat redg. clear.
simpl.
repeat redg.
rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 1))) (b2:=   (if_then_else_B
              (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
              (if_then_else_B
                 (if_then_else_B
                    (if_then_else_B
                       (if_then_else_B (EQ_M (to (f mphi1)) (i 2))
                          (EQ_M (to (f mphi0)) (i 1)) FAlse)
                       (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)
                       FAlse) (EQ_M (act (f mphi0)) new) FAlse)
                 (EQ_M (m (f mphi2))
                    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))
                 FAlse) FAlse)).

rewrite <- IFSAME_M with (b:= (EQ_M (reveal (f mphi3)) (i 1))) .
 apply breq_msgeq'.

assert(  (subbol_msg' (EQ_M (reveal (f mphi3)) (i 1)) TRue
      (if_then_else_M
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                  (EQ_M (to (f mphi0)) (i 1)) FAlse)
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) FAlse)
            (EQ_M (act (f mphi0)) new) FAlse)
         (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
         (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                        (EQ_M (to (f mphi1)) (i 1)) FAlse)
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse) 
            (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O))) #   (if_then_else_M
         (if_then_else_B
            (if_then_else_B
               (if_then_else_B TRue
                  (EQ_M (to (f mphi0)) (i 1)) FAlse)
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) FAlse)
            (EQ_M (act (f mphi0)) new) FAlse)
         (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))
         (if_then_else_M
            (if_then_else_B
               (if_then_else_B
                  (if_then_else_B
                     (if_then_else_B TRue
                        (EQ_M (to (f mphi1)) (i 1)) FAlse)
                     (EQ_M (to (f mphi0)) (i 1)) FAlse)
                  (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)
                  FAlse) (EQ_M (act (f mphi0)) new) FAlse)
            (exp (pi1 (ggen (N 0))) (m (f mphi1)) (rr (N 1))) O))).
unfold subbol_msg'. 
assert(check_eq_msg (reveal (f mphi3)) (reveal (f mphi3)) &&
                         check_eq_msg (i 1) (i 1) = true).

simpl.
reflexivity. rewrite H. repeat redg. simpl.  clear. reflexivity. rewrite H. clear  .
unfold subbol_msg'. 
assert(check_eq_msg (reveal (f mphi3)) (reveal (f mphi3)) &&
                         check_eq_msg (i 1) (i 1) = true).
simpl. reflexivity. 
rewrite H.  repeat redg.
simpl.
rewrite andB_comm with (b1:= (EQ_M (to (f mphi1)) (i 2))) (b2:=  (EQ_M (to (f mphi0)) (i 1))).
rewrite andB_assoc with (b2:= (EQ_M (to (f mphi1)) (i 2))) (b1:=   (EQ_M (to (f mphi0)) (i 1)) ) (b3:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)). 
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 1))) (b2:=   ((EQ_M (to (f mphi1)) (i 2)) &
               (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue))) (b3:= (EQ_M (act (f mphi0)) new)). 

rewrite andB_assoc with (b1:=  (EQ_M (to (f mphi0)) (i 1)) ) (b2:=  (((EQ_M (to (f mphi1)) (i 2)) &
             (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
            (EQ_M (act (f mphi0)) new))) (b3:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite <- andB_assoc  with  (b1:= (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))  (b2 :=  (EQ_M (to (f mphi0)) (i 1)))   (b3:= 
             ((((EQ_M (to (f mphi1)) (i 2)) &
              (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
             (EQ_M (act (f mphi0)) new)) &
            (EQ_M (m (f mphi2))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
rewrite andB_comm with (b1:=  (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:= (EQ_M (to (f mphi0)) (i 1))).
rewrite andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 1))) (b2:=   (EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_elm' with (b1:=  (EQ_M (to (f mphi0)) (i 1))) (b2:=  ((EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))) &
         ((((EQ_M (to (f mphi1)) (i 2)) &
            (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) &
           (EQ_M (act (f mphi0)) new)) &
          (EQ_M (m (f mphi2))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))))).

(***********LHS*****************)
clear.
rewrite  andB_assoc with (b1:= (EQ_M (to (f mphi0)) (i 1))) (b2:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b3:=   (EQ_M (act (f mphi0)) new)).

rewrite andB_elm' with (b1:=  (EQ_M (to (f mphi0)) (i 1))) (b2:=  ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
       (EQ_M (act (f mphi0)) new))).
 apply breq_msgeq'. simpl.

(****************RHS**************)
rewrite andB_comm with ( b1:= (EQ_M (to (f mphi1)) (i 2))) (b2:=    (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)).
rewrite andB_assoc with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:=  (EQ_M (to (f mphi1)) (i 2))) (b3:=  (EQ_M (act (f mphi0)) new)).
rewrite andB_comm with (b1:= (EQ_M (to (f mphi1)) (i 2))) (b2:= (EQ_M (act (f mphi0)) new)).
repeat redg.
repeat rewrite IFTFb.
rewrite andB_assoc with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) )
              (b2:= ((EQ_M (act (f mphi0)) new) & (EQ_M (to (f mphi1)) (i 2)))) (b3:=  (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_comm with  (b1:=  (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b2:=   (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
           (((EQ_M (act (f mphi0)) new) & (EQ_M (to (f mphi1)) (i 2))) &
            (EQ_M (m (f mphi2))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
rewrite andB_assoc with (b1:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:=  (((EQ_M (act (f mphi0)) new) & (EQ_M (to (f mphi1)) (i 2))) &
          (EQ_M (m (f mphi2))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))) (b3:= (EQ_M (m (f mphi1))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_elm' with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:=  ((((EQ_M (act (f mphi0)) new) & (EQ_M (to (f mphi1)) (i 2))) &
          (EQ_M (m (f mphi2))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))) &
         (EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))).

(**********************LHS*******************)
rewrite andB_elm' with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:= (EQ_M (act (f mphi0)) new)).
aply_breq.
(******************RHS*******************)

rewrite andB_assoc with (b1:= (EQ_M (act (f mphi0)) new)) (b2:=   (EQ_M (to (f mphi1)) (i 2))) (b3:=  (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_assoc with (b1:= (  (EQ_M (act (f mphi0)) new))) (b2:=   ((EQ_M (to (f mphi1)) (i 2)) &
            (EQ_M (m (f mphi2))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))) (b3:=  (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_elm' with (b1:=  (EQ_M (act (f mphi0)) new) ) (b2:=  (((EQ_M (to (f mphi1)) (i 2)) &
          (EQ_M (m (f mphi2))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))) &
         (EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))).

aply_breq.
rewrite andB_comm with (b1:= (EQ_M (to (f mphi1)) (i 2))) (b2:=  (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).

rewrite andB_assoc with (b2:= (EQ_M (to (f mphi1)) (i 2))) (b1:=  (EQ_M (m (f mphi2))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))) (b3:= (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_elm' with (b1:=  (EQ_M (m (f mphi2))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))) (b2:=  ((EQ_M (to (f mphi1)) (i 2)) &
         (EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))).


repeat redg.
rewrite <- IFSAME_M with (b:=   (EQ_M (m (f mphi2))
           (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))). 
pose proof (EQbrmsg_msg'' (m (f mphi2)) (m (f mphi2))  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))) (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1))) (exp (pi1 (ggen (N 0))) (m (f mphi2)) (rr (N 1)))). simpl in H.
rewrite H. repeat redg.

aply_breq.
clear .
rewrite commexp.
rewrite IFSAME_M.
reflexivity.
 (****************************subgoal***************)
simpl.
repeat redg. reflexivity.
 
(**************subgoal***********)
unfold subbol_msg'.
assert( check_eq_msg (reveal (f mphi3)) (reveal (f mphi3)) &&
                   check_eq_msg (i 1) (i 1) = true).
simpl. reflexivity. 

repeat redg. reflexivity. 
apply EQM in H.
rewrite H. reflexivity.
Qed.