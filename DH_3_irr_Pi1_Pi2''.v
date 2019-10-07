Load "tact_DH_3_irr".










Theorem Pi1_Pi2'': phi7 #### phi37.
Proof. unfold phi7, phi37, phi6, phi36. simpl. 
  
 
assert(H: (ostomsg t15) # (ostomsg t35)). 
   
simpl.
  Eval compute in size_msg ( (if_then_else_M (EQ_M (reveal x1) (i 1)) O
      (if_then_else_M (EQ_M (reveal x1) (i 2)) O
         (if_then_else_M (EQ_M (reveal x1) (i 3)) O
            (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
               qa100_ss
               (if_then_else_M (EQ_M (to x1) (i 2)) qa010_ss
                  (if_then_else_M (EQ_M (to x1) (i 3)) qa001_ss O))))))).
repeat (unfold andB;  aply_andB_elm) .  
aply_breq.
repeat (false_to_sesns_all ;  aply_breq ;  redg). 

 Focus 2.  repeat redg.  reflexivity. 
Ltac rew_andB_elm := 
match goal with 
| [|- context[ if_then_else_M (if_then_else_B ?B1 ?B2 FAlse) ?T1 ?T2] ] => rewrite andB_elm' with (b1:= B1) (b2:= B2)
end.

repeat rew_andB_elm. 
repeat (unfold andB;  aply_andB_elm)    .  

 repeat false_to_sesns_all. 
repeat  aply_breq.
repeat   redg.

 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.

 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.

repeat rewrite andB_elm' with (b1:= (EQ_M (to (f mphi0)) (i 1))) (b2:= (EQ_M (act (f mphi0)) new)).
rew_lhs 2 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 2 . omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.

 apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb.
 apply breq_msgeq'.   simpl.  repeat redg.  repeat rewrite IFTFb.
apply breq_msgeq1'.   simpl.  repeat redg.  repeat rewrite IFTFb.
apply breq_msgeq1'. simpl.  repeat redg.  repeat rewrite IFTFb.


apply breq_msgeq1'.   simpl.  repeat redg.  repeat rewrite IFTFb.
rew_lhs 2 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 2 . omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.
 apply breq_msgeq'.  simpl.   repeat redg. repeat rewrite IFTFb.

repeat rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi2)) (i 1))) (b2:=   (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)).


apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
repeat rewrite andB_elm' with (b1:= (EQ_M (to (f mphi1)) (i 1))) (b2:=  (EQ_M (act (f mphi1)) new)).
rew_lhs 1 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 1 . omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.

reflexivity. simpl. 

 
rew_lhs 1 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 1 . omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
rew_lhs 1 . omega. aply_eval_lhs.
rew_lhs 2 . omega. aply_eval_lhs.
rew_rhs 1 . omega. aply_eval_rhs.
rew_rhs 2 . omega. aply_eval_rhs.
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb. reflexivity. 
simpl.  repeat redg. repeat rewrite IFTFb .
 apply breq_msgeq1'. simpl. repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
rew_lhs 2 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 2 . omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.
apply breq_msgeq'. simpl.  repeat redg. repeat rewrite IFTFb. 
 
rewrite andB_assoc with (b1:= (EQ_M (reveal (f mphi3)) (i 3))) (b2:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b3:=  (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))).
rewrite andB_assoc with (b1:=  (EQ_M (reveal (f mphi3)) (i 3))) (b2:=  ((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
            (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))))) (b3 :=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 3))) (b2:=   (((if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) &
          (EQ_M (m (f mphi1))
             (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
apply breq_msgeq'. simpl.  repeat redg. repeat rewrite IFTFb. 
rewrite <- IFSAME_M with (b:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) .
rewrite andB_assoc with (b1:= (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:=   (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b3:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:=  (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue)) (b2:=  ((EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
apply breq_msgeq'. simpl.  repeat redg. repeat rewrite IFTFb. 
rewrite <- IFSAME_M with (b:=   (if_then_else_B
           (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
           (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))) FAlse)).
  repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) (b:= (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))) .
simpl .
apply breq_msgeq'. simpl.  repeat redg. repeat rewrite IFTFb. reflexivity.
simpl. repeat redg.
rewrite <- IFSAME_M with (b:= (if_then_else_B
           (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
              (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
              FAlse)
           (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))) FAlse)).
rewrite andB_assoc with (b1:= (EQ_M (reveal (f mphi3)) (i 1))) (b2:= (EQ_M (m (f mphi1))
               (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b3:= (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
repeat rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi3)) (i 1))) (b2:=  ((EQ_M (m (f mphi1))
          (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))) &
       (EQ_M (m (f mphi2))
          (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).

apply breq_msgeq'.


 simpl.  repeat redg. repeat rewrite IFTFb. 
rewrite <- IFSAME_M with (b:=  (if_then_else_B
           (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))
           (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))) FAlse)).
 repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) (b:= (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))) .
simpl. 
repeat rewrite andB_comm with (b1:= (EQ_M (m x2) (grn 1))) (b2:=  (EQ_M (m (f mphi2))
         (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
repeat rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))) (b:= (EQ_M (m (f mphi1))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) .
simpl. 
rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
apply breq_msgeq'. simpl.  reflexivity. 

simpl. 
repeat redg.  reflexivity. simpl. redg.  reflexivity.
simpl.

repeat redg.   reflexivity. 
simpl. redg.
rewrite andB_assoc with (b1:=  (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
                 (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) FAlse)) (b2:=  (EQ_M (m (f mphi1))
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1))))) (b3:=  (EQ_M (m (f mphi2))
              (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2))))).
rewrite andB_elm' with (b1:= (if_then_else_B (EQ_M (reveal (f mphi3)) (i 1))
           (if_then_else_B (EQ_M (act (f mphi2)) new) FAlse TRue) FAlse))(b2:=   ((EQ_M (m (f mphi1))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 1)))) &
         (EQ_M (m (f mphi2))
            (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (rr (N 2)))))).
apply breq_msgeq'. simpl. redg. 
reflexivity.  simpl. redg. reflexivity. 
simpl. reflexivity. 
reflexivity. 
reflexivity. simpl.
rew_lhs  1 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 1 . omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.

apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
repeat rewrite andB_elm' with (b1:= (EQ_M (to (f mphi1)) (i 1))) (b2:= (EQ_M (act (f mphi1)) new)).
rew_lhs  2 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 2 . omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq1'.  simpl.  repeat redg.  repeat rewrite IFTFb. reflexivity.
simpl.
rew_lhs  1 . omega. aply_eval_lhs.
rew_lhs 2 . omega. aply_eval_lhs.
rew_rhs 1 . omega. aply_eval_rhs.
rew_rhs 2 . omega. aply_eval_rhs.
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
repeat rewrite andB_elm' with (b1:= (EQ_M (to (f mphi1)) (i 1))) (b2:= (EQ_M (act (f mphi1)) new)).
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. reflexivity.  reflexivity.


apply EQM in H. 
rewrite H. 
assert(H1: (ostomsg t16) # (ostomsg t36)). 
simpl.
 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
 apply breq_msgeq1'.  simpl.  repeat redg. repeat  rewrite IFTFb.
 repeat rewrite andB_elm' with (b1:= (EQ_M (to (f mphi0)) (i 1))) (b2:= (EQ_M (act (f mphi0)) new)).
 apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb. simpl. redg. 
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.
 apply breq_msgeq1'.  simpl.  repeat redg. repeat  rewrite IFTFb.
rew_lhs  2 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 2 . omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb. 
repeat rewrite andB_elm' with (b1:= (EQ_M (reveal (f mphi2)) (i 1))) (b2:= (if_then_else_B (EQ_M (act (f mphi1)) new) FAlse TRue)).
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
 apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb.

rew_lhs  1 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 1 . omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.
 reflexivity.
simpl.  repeat redg. repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg. repeat rewrite IFTFb. 
 apply breq_msgeq1'.  simpl.  repeat redg.  repeat rewrite IFTFb.
apply breq_msgeq'.  simpl.  repeat redg. repeat rewrite IFTFb.
reflexivity. 
simpl. 
rew_lhs  1 . omega. aply_eval_lhs.
rew_lhs 2 . omega. aply_eval_lhs.
rew_rhs 1 .  omega. aply_eval_rhs.
rew_rhs 2 . omega. aply_eval_rhs.
apply breq_msgeq'.  simpl.  repeat redg.  repeat rewrite IFTFb.
reflexivity. reflexivity. 
simpl. 
apply breq_msgeq1'.  simpl.  repeat redg.  repeat rewrite IFTFb.
apply breq_msgeq1'.  simpl.  repeat redg.  repeat rewrite IFTFb. reflexivity. 
simpl. repeat redg.  repeat rewrite IFTFb.
rew_lhs  1 . omega. aply_eval_lhs.
rew_lhs 3 . omega. aply_eval_lhs.
rew_rhs 1 .  omega. aply_eval_rhs.
rew_rhs 3 . omega. aply_eval_rhs.
apply breq_msgeq'.  simpl.  repeat redg.   repeat rewrite IFTFb. 
repeat rewrite andB_elm' with (b1:=(EQ_M (reveal (f mphi2)) (i 2))) (b2:= (EQ_M (to (f mphi0)) (i 2))).
apply breq_msgeq1'.  simpl.  repeat redg.   repeat rewrite IFTFb.
reflexivity.
Qed.
