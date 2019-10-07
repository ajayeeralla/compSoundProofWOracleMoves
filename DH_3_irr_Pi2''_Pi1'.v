Load "tact_DH_3_irr".
  Ltac rew_assoc_lr  :=
match goal with 
| [ |- context [if_then_else_M  (if_then_else_B (if_then_else_B ?B1 (EQ_M (m x2) (grn 1)) FAlse) (EQ_M (m x3) (grn 2)) FAlse) ?T1 ?T2 ] ] => rewrite andB_assoc with (b1:= B1) (b2:= (EQ_M (m x2) (grn 1))) (b3:= (EQ_M (m x3) (grn 2)))
end.

Ltac rew_comm_lr :=
match goal with 
| [ |- context [if_then_else_M (if_then_else_B ?B1 (if_then_else_B (EQ_M (m x2) (grn 1)) (EQ_M (m x3) (grn 2))  FAlse) FAlse) ?T1 ?T2 ] ] => rewrite andB_comm with (b1:=  B1) (b2:=(if_then_else_B (EQ_M (m x2) (grn 1)) (EQ_M (m x3) (grn 2))  FAlse) ) 
end.

Ltac if_mx2rn2 :=
 match goal with 
| [|- context[ if_then_else_M (if_then_else_B (if_then_else_B (EQ_M (m x2) (grn 1)) (EQ_M (m x3) (grn 2))  FAlse) ?B1 FAlse)  (exp (G 0) (m x2) (r 2)) ?T2] ]=>   rewrite andB_assoc with (b1:= (EQ_M (m x2) (grn 1))) (b2:=  (EQ_M (m x3) (grn 2))) (b3:= B1) 
end.

Ltac if_mx3rn1:= 
match goal with 
| [|- context[ if_then_else_M (if_then_else_B (if_then_else_B (EQ_M (m x2) (grn 1)) (EQ_M (m x3) (grn 2))  FAlse) ?B1 FAlse)  (exp (G 0) (m x3) (r 1)) ?T2] ]=> rewrite andB_comm with (b1:= (EQ_M (m x2) (grn 1))) (b2:=  (EQ_M (m x3) (grn 2))) ; try   rewrite andB_assoc with (b1:= (EQ_M (m x3) (grn 2))) (b2:=  (EQ_M (m x2) (grn 1))) (b3:= B1)  
end.

Ltac aply_eqbr_mx2 :=

match goal with 
| [|- context [if_then_else_M (if_then_else_B (EQ_M (m x2) (grn 1) ) ?B FAlse) (exp (G 0) (m x2) (r 2))  ?T2 ] ] =>   rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2)) (b:= B)  (m3:= (exp (G 0) (m x2) (r 2))) 
end.


  Ltac aply_eqbr_mx3 :=

match goal with 
| [|- context [if_then_else_M (if_then_else_B (EQ_M (m x3) (grn 2) ) ?B FAlse) (exp (G 0) (m x3) (r 1))  ?T2 ] ] =>   rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3)) (b:= B)  (m3:= (exp (G 0) (m x3) (r 1))) 
end.


Ltac rew_back_mx2 := 
match goal with 
| [ |- context[ if_then_else_M (if_then_else_B (EQ_M (m x2) (grn 1)) (if_then_else_B   (EQ_M (m x3) (grn 2)) ?B1 FAlse) FAlse) ?T1 ?T2] ] =>
rewrite <- andB_assoc with (b1:= (EQ_M (m x2) (grn 1))) (b2:= (EQ_M (m x3) (grn 2))) (b3:= B1)
end.



Ltac rew_back_mx3 := 
match goal with 
| [ |- context[ if_then_else_M (if_then_else_B (EQ_M (m x3) (grn 2)) (if_then_else_B   (EQ_M (m x2) (grn 1)) ?B1 FAlse) FAlse) ?T1 ?T2] ] =>
rewrite <- andB_assoc with (b1:= (EQ_M (m x3) (grn 2))) (b2:= (EQ_M (m x2) (grn 1))) (b3:= B1) ; try rewrite andB_comm with   (b1:= (EQ_M (m x3) (grn 2))) (b2:= (EQ_M (m x2) (grn 1)))
end.

Ltac rew_commexp :=
 rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).
(*
pose proof (andB_assoc B1 B2 B3); 
match goal with
| [ H :  context [(?B1 & ?B2 ) & ?B3 ]  |- _ ] => rewrite H ; clear H
end
end.


*)
Theorem pi2''_pi2': phi37 ~ phi47.


Proof. 
unfold phi37, phi47.
  simpl.
 (******************thn***************************)
(******assert(thn: qc01_ss # qd01_ss).****)
assert( (ostomsg t35) # (ostomsg t45)).
simpl.

assert(qc100_ss # qd100_ss).
repeat unf. 
repeat unfold mx2rn2.
repeat unfold mx3rn1.
repeat unfold andB.
repeat rew_assoc_lr.
repeat unfold andB. 
repeat rew_comm_lr. 
repeat unfold andB. 
 repeat if_mx2rn2.  
repeat unfold andB. 
  repeat aply_eqbr_mx2. 
 repeat if_mx3rn1. 
repeat unfold andB. 
repeat  aply_eqbr_mx3. 
simpl.
repeat rew_commexp. reflexivity.


assert(qc001_ss # qd001_ss).

repeat unf. 
repeat unfold mx2rn2.
repeat unfold mx3rn1.
repeat unfold andB.
repeat rew_assoc_lr.
repeat unfold andB. 
repeat rew_comm_lr. 
repeat unfold andB. 
 repeat if_mx2rn2.  
repeat unfold andB. 
  repeat aply_eqbr_mx2. 
 repeat if_mx3rn1. 
repeat unfold andB. 
repeat  aply_eqbr_mx3. 
simpl.
repeat rew_commexp. reflexivity.

assert(qc010_ss # qd010_ss).
unfold qc010_ss, qd010_ss. 
repeat unf. 
repeat unfold mx2rn2.
repeat unfold mx3rn1.
repeat unfold andB.
repeat rew_assoc_lr.
repeat unfold andB. 
repeat rew_comm_lr. 
repeat unfold andB. 
 repeat if_mx2rn2.  
repeat unfold andB. 
  repeat aply_eqbr_mx2. 
 repeat if_mx3rn1. 
repeat unfold andB. 
repeat  aply_eqbr_mx3. 
simpl.
repeat rew_commexp. reflexivity.
rewrite H, H0, H1.  reflexivity. 
(*********************************************************************************)
assert((ostomsg t36) # (ostomsg t46)).
simpl. 

assert(qc100_sss # qd100_sss). 
 unfold qc100_sss, qd100_sss. 




assert(qc200_ss # qd200_ss).
unfold qc200_ss, qd200_ss. 
assert(qc201_s # qd201_s).
repeat  unf.  
repeat unfold mx2rn2.
repeat unfold mx3rn1.
repeat unfold andB.
repeat rew_assoc_lr.
repeat unfold andB. 
repeat rew_comm_lr. 
repeat unfold andB. 
 repeat if_mx2rn2.  
repeat unfold andB. 
  repeat aply_eqbr_mx2. 
  if_mx3rn1.  if_mx3rn1. 
repeat unfold andB. 
repeat  aply_eqbr_mx3. 
simpl.

repeat rew_commexp.
repeat rew_back_mx2.
repeat rew_back_mx3.
 reflexivity.

simpl; repeat unfold andB. 
repeat rew_back_mx2.
repeat rew_back_mx3.

reflexivity. 
assert(qc100_ss # qd100_ss).
repeat unf. 



 rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2.
  repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) (b:= (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                             (EQ_M (to x2) (i 3))) & 
                            (EQ_M (to x1) (i 1))) &
                           (notb (EQ_M (act x3) new))) & 
                          (EQ_M (act x1) new)) & (EQ_M (m x3) (grn 2)))).


simpl. 
repeat rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x3) (i 1))) &
                                      (EQ_M (to x2) (i 3))) &
                                     (EQ_M (to x1) (i 1))) &
                                    (notb (EQ_M (act x3) new))) &
                                   (EQ_M (act x1) new)) &
                                  (EQ_M (m x2) (grn 1))))  (b2:=  (EQ_M (m x3) (grn 2))) .
unfold mx3rn1.
repeat rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))).


 repeat rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))) (b3:= (EQ_M (m x3) (grn 2))). 
repeat rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))). 
repeat rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
repeat rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2.

  repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))). simpl.
pose proof(commexp). 
  repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity.



assert(qc010_ss # qd010_ss).
repeat unf. 
unf_m.   repeat unf.
 rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2.
  repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) (b:= (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                             (EQ_M (to x2) (i 3))) & 
                            (EQ_M (to x1) (i 1))) &
                           (notb (EQ_M (act x3) new))) & 
                          (EQ_M (act x1) new)) & (EQ_M (m x3) (grn 2)))).


simpl. 
repeat rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x3) (i 1))) &
                                      (EQ_M (to x2) (i 3))) &
                                     (EQ_M (to x1) (i 1))) &
                                    (notb (EQ_M (act x3) new))) &
                                   (EQ_M (act x1) new)) &
                                  (EQ_M (m x2) (grn 1))))  (b2:=  (EQ_M (m x3) (grn 2))) .
unfold mx3rn1.
repeat rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))).


 repeat rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))) (b3:= (EQ_M (m x3) (grn 2))). 
repeat rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))). 
repeat rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
repeat rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2.

  repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))). simpl.
pose proof(commexp). 
  repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity.
assert(qc001_ss # qd001_ss).
unf_m.   repeat unf.
 rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2.
  repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) (b:= (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                             (EQ_M (to x2) (i 3))) & 
                            (EQ_M (to x1) (i 1))) &
                           (notb (EQ_M (act x3) new))) & 
                          (EQ_M (act x1) new)) & (EQ_M (m x3) (grn 2)))).


simpl. 
repeat rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x3) (i 1))) &
                                      (EQ_M (to x2) (i 3))) &
                                     (EQ_M (to x1) (i 1))) &
                                    (notb (EQ_M (act x3) new))) &
                                   (EQ_M (act x1) new)) &
                                  (EQ_M (m x2) (grn 1))))  (b2:=  (EQ_M (m x3) (grn 2))) .
unfold mx3rn1.
repeat rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))).


 repeat rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))) (b3:= (EQ_M (m x3) (grn 2))). 
repeat rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))). 
repeat rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
repeat rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2.

  repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))). simpl.
pose proof(commexp). 
  repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity.
rewrite H, H0, H1.  reflexivity. 
assert((ostomsg t36) # (ostomsg t46)).
simpl. 
(******************************* qc100_sss #  qd100_sss*********************************)
assert( qc100_sss #  qd100_sss).
unf_m. 
assert(qc200_ss # qd200_ss).

unfold qc200_ss, qd200_ss.
assert(qc210_s # qd210_s).
unf_m.
assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 
rewrite H0. reflexivity. 
(***********************)
assert(qc201_s # qd201_s).
unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 
rewrite H1. reflexivity.
rewrite H0, H1. reflexivity.
 (*******************************************************)
(********************************************************)

assert(qc110_ss # qd110_ss).
unfold qc110_ss, qd110_ss.


assert(qc210_s # qd210_s).
unf_m.
assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 
rewrite H1. reflexivity. 
(**************************************)
assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 
rewrite H2. reflexivity. 
rewrite H1, H2. reflexivity. 

(*********************************************)
assert(qc101_ss # qd101_ss).
unf_m.

assert(qc201_s # qd201_s).
unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 
rewrite H2. reflexivity. 
rewrite  H2.

(**************************************)
assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 

rewrite H3. reflexivity. 
rewrite  H3. reflexivity. 
rewrite  H0, H1, H2.  reflexivity.
(****************************** qc010_sss #  qd010_sss******************************************************)

assert(qc010_sss #  qd010_sss).
unf_m.

assert(qc110_ss # qd110_ss). 
unf_m.


assert(qc210_s # qd210_s).
unf_m.
assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 
rewrite H1. reflexivity. 
(**************************************)
assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 
rewrite H2. reflexivity. 
rewrite H1, H2. reflexivity. 
(*********************************************)

assert( qc011_ss #  qd011_ss).
unf_m. 

assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 

 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
rewrite H2. reflexivity. 
rewrite H2. reflexivity. 
rewrite H1, H2.
reflexivity. 
(**********************qc001_sss # qd001_sss**************************************)

assert(qc001_sss # qd001_sss).
unf_m.

assert( qc011_ss #  qd011_ss).
unf_m. 

assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 

 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
rewrite H2. reflexivity. 
rewrite H2. reflexivity. 
rewrite  H2.


assert(qc101_ss # qd101_ss).
unf_m.

assert(qc201_s # qd201_s).
unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 

rewrite H3. reflexivity. 

(***********************************************************************************)
assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 

 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
rewrite H4. reflexivity. 
rewrite H3, H4. reflexivity. 
rewrite  H3. reflexivity. 
rewrite H0, H1, H2. reflexivity.
(******************************t37 # t47******************************)

assert ((ostomsg t37) # (ostomsg t47)).
simpl. 
(*****************  qc100_ssss #   qd100_ssss************************)


assert(qc100_ssss # qd100_ssss).
unf_m.


assert( qc200_sss #  qd200_sss).
unf_m. 
assert(qc210_ss # qd210_ss).
unf_m.
(***************************)
assert(qc220_s # qd220_s).
unf_m.
(*******************)
assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
(*****************)
rewrite H1. reflexivity. 
(*****************************)
assert(qc211_s # qd211_s).
unf_m.
(*******************)
assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
(*****************)

rewrite H2. reflexivity. 
(***********************************)
rewrite H1, H2. reflexivity. 

(************************************************)
assert(qc201_ss # qd201_ss).
unf_m.
assert(qc202_s # qd202_s). 

unf_m. 

(************)
assert(qc212 # qd212).
unf_m.




rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
(*************)
rewrite H2.
reflexivity. 
(************)
 repeat rewrite H2. 

assert(qc211_s # qd211_s).
unf_m.

(*******************)
assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
(************************************)
repeat rewrite H3.
reflexivity. 
rewrite H3.
reflexivity. 
rewrite H1, H2.
reflexivity. 


(**********************************************************************************)
assert(qc110_sss # qd110_sss).
unf_m.
assert( qc120_ss #  qd120_ss).
unf_m.
assert(qc220_s # qd220_s). 
unf_m.
(************************)

assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
(********************************************************************)
rewrite H2.
reflexivity. 
(************************************)
assert(qc121_s # qd121_s). 
unf_m.

(************************)

assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
repeat rewrite H3.  
reflexivity. 
rewrite H2, H3 . reflexivity. 
(******************************)
assert( qc120_ss #  qd120_ss).
unf_m.
assert(qc220_s # qd220_s). 
unf_m.
(************************)

assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
(********************************************************************)


assert(qc210_ss # qd210_ss).
unf_m.
(***************************)
assert(qc220_s # qd220_s).
unf_m.  rewrite H3.  reflexivity.  repeat rewrite H4. 

assert (qc211_s # qd211_s).
unf_m. repeat rewrite H3. reflexivity.  rewrite H5.  reflexivity.  rewrite H3. reflexivity. 
rewrite H3.
assert(qc121_s # qd121_s). 
unf_m.
assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity.  rewrite H4. reflexivity. 
rewrite  H4.  reflexivity. rewrite H2. 

assert(qc210_ss # qd210_ss).
unf_m. 
(***************************)
assert(qc220_s # qd220_s).
unf_m. (*******************)
assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).    reflexivity. 
(*****************)
 rewrite H4.  reflexivity.  repeat rewrite H4. 

assert (qc211_s # qd211_s).
unf_m.

 (*******************)
assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).    reflexivity. 
(*****************)

 repeat rewrite H5. reflexivity.  rewrite H5.  reflexivity.  

assert(qc111_ss # qd111_ss).
unf_m.

assert(qc121_s # qd121_s). 
unf_m.
assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity.


  rewrite H5. reflexivity.  repeat rewrite H5.
assert(qc112_s # qd112_s).
unf_m.

(************)
assert(qc212 # qd212).
unf_m.




rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).   reflexivity. 
(*************)

rewrite  H6.  reflexivity. rewrite H6. 
assert(qc211_s # qd211_s).
unf_m. 

assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity.
repeat rewrite H7. reflexivity. rewrite H7. reflexivity. rewrite  H4, H5. reflexivity. 


(********************************************************************************)
assert(qc101_sss # qd101_sss).
unf_m.

assert(qc201_ss # qd201_ss).
unf_m.
assert(qc202_s # qd202_s). 

unf_m. 

(************)
assert(qc212 # qd212).
unf_m.




rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
(*************)
rewrite H3.
reflexivity. 
(************)
 repeat rewrite H3. 

assert(qc211_s # qd211_s).
unf_m.

(*******************)
assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 

(*****************)
rewrite H4. reflexivity. 
rewrite  H4. reflexivity. 

assert (qc102_ss # qd102_ss).
(*****************************)
assert(qc211_s # qd211_s).
unf_m.
(*******************)
assert(qc221 # qd221). 
unf_m.


 rewrite andB_assoc with  (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:= (((((((EQ_M (reveal x6) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))). 
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 
repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
(*****************)

rewrite H2. reflexivity. 
(***********************************)
rewrite H1, H2. reflexivity. 



rewrite H2.
reflexivity. 
assert(qc210_ss
m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
rewrite H2. reflexivity. 
(**************************************)
assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 
rewrite H3. reflexivity. 
rewrite H2, H3. reflexivity. 

(*********************************************)
assert(qc101_ss # qd101_ss).
unf_m.

assert(qc201_s # qd201_s).
unf_m.

assert(qc211 # qd211).
 repeat unf.
 
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
rewrite H3. reflexivity. 


(**************************************)
assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 

rewrite H4. reflexivity. 
rewrite  H3, H4 . reflexivity. 
rewrite  H1, H2, H3.  reflexivity.
(****************************** qc010_sss #  qd010_sss******************************************************)

assert(qc010_sss #  qd010_sss).
unf_m.

assert(qc110_ss # qd110_ss). 
unf_m.


assert(qc210_s # qd210_s).
unf_m.
assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
rewrite H2. reflexivity. 
(**************************************)
assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity. 
rewrite H3. reflexivity. 
rewrite H2, H3. reflexivity. 
(*********************************************)

assert( qc011_ss #  qd011_ss).
unf_m. 

assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 

 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
rewrite H3. reflexivity. 
rewrite H3. reflexivity. 
rewrite H2, H3.
reflexivity. 
(**********************qc001_sss # qd001_sss**************************************)

assert(qc001_sss # qd001_sss).
unf_m.

assert( qc011_ss #  qd011_ss).
unf_m. 

assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 

 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 
rewrite H3. reflexivity. 
rewrite H3. reflexivity. 
rewrite  H3.


assert(qc101_ss # qd101_ss).
unf_m.

assert(qc201_s # qd201_s).
unf_m.

assert(qc211 # qd211).
 repeat unf.
 
(**************)
 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).  reflexivity. 

rewrite H4. reflexivity. 

(***********************************************************************************)
assert(qc111_s # qd111_s).

unf_m.

assert(qc211 # qd211).
 repeat unf.
 

 rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .


simpl. 
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))).
rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

rewrite andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new))) (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))).

 rewrite <-andB_assoc with (b1:= ((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
              (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)))(b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 2)) & (EQ_M (to x3) (i 1))) &
                 (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
               (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
             (EQ_M (m x3) (grn 2)))) (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
simpl. 

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x5) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
                  (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
                (EQ_M (m x2) (grn 1)))).

rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl. 

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).    reflexivity. 
rewrite H5. reflexivity. 
rewrite H4, H5. reflexivity. 
rewrite  H4. reflexivity. 
rewrite H1, H2, H3. reflexivity.





rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))). 
 rewrite andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .
 rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
 rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
 rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
 unfold mx2rn2.
 rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) .

simpl. 
 rewrite andB_comm with (b2:= (EQ_M (m x3) (grn 2))). 
 rewrite <- andB_assoc with (b2:= (EQ_M (m x3) (grn 2))).
 rewrite andB_comm with (b1 := (EQ_M (m x2) (grn 1))). 
 rewrite andB_assoc with (b1 := (EQ_M (m x3) (grn 2))).
 

 unfold mx3rn1.
 rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))).
simpl. 
 rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))).

 reflexivity.

 repeat rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))) (b3:= (EQ_M (m x3) (grn 2))). 
repeat rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))) (b2:= (EQ_M (m x3) (grn 2))). 
repeat rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
repeat rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2.

  repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))). simpl.
pose proof(commexp). 
  repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity.

 repeat rewrite andB_comm with  (b2:=  (EQ_M (m x3) (grn 2))) .
unfold mx3rn1.
repeat rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))) (b:= (((((((EQ_M (reveal x4) (i 1)) &
                                       (EQ_M (to x3) (i 1))) &
                                      (EQ_M (to x2) (i 3))) &
                                     (EQ_M (to x1) (i 1))) &
                                    (notb (EQ_M (act x3) new))) &
                                   (EQ_M (act x1) new)) &
                                  (EQ_M (m x2) (grn 1))) ) . simpl.

 repeat rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
repeat rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
repeat rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
repeat rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2.
repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) (b:= ) .
simpl. 
simpl. 
pose proof(EQBRmsg_msg'  (((((((EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x3) (i 1))) & 
                                (EQ_M (to x2) (i 2))) & 
                               (EQ_M (to x1) (i 1))) &
                              (notb (EQ_M (act x3) new))) &
                             (EQ_M (act x1) new)) & 
                            (EQ_M (m x2) (grn 1))) (m x3) (m x3) (grn 2)  (exp (G 0) (m x3) (r 1)) 
 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x2) (i 2))
                                    (exp (G 0) (m x2) (r 2))
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x1) (i 2)) mx1rn2
                                       (if_then_else_M
                                          ((((EQ_M (reveal x4) (i 1)) &
                                             (EQ_M (to x3) (i 1))) &
                                            (EQ_M (to x1) (i 1))) &
                                           (notb (EQ_M (act x3) new))) &
                                          (EQ_M (act x1) new)
                                          (exp (G 0) (m x3) (r 1))
                                          (if_then_else_M
                                             ((((EQ_M (reveal x4) (i 1)) &
                                                (EQ_M (to x2) (i 1))) &
                                               (EQ_M (to x1) (i 1))) &
                                              (notb (EQ_M (act x2) new))) &
                                             (EQ_M (act x1) new) mx2rn1 O))))).
simpl in H.
rewrite H; clear.
rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
reflexivity. Qed.
