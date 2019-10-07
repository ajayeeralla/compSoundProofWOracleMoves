Load "tact_DH_3_iir".
 


Theorem pi2''_pi2': phi38 ~ phi48.

Proof.  
repeat unf_i. simpl. 




assert((ostomsg t35) # (ostomsg t45)).
simpl.
assert( qc100_ss # qd100_ss). 
 unf_m. simpl. 


assert(qc200_s # qd200_s).
unf_m ; simpl. 

assert(qc201 # qd201).
unf_m; simpl.







 
rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2. 

 repeat rewrite EQBRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))). simpl.

repeat rewrite andB_comm with  (b2:=  (EQ_M (m x3) (grn 2))) .
 repeat rewrite EQBRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1))). simpl.

 repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (y:= (rr (N 2)))(x:= (rr (N 1))). simpl. reflexivity. 
unfold grn21. 
reflexivity.
rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))) .

pose proof(commexp). 
  repeat rewrite commexp with (G:= (pi1 (ggen (N 0)))) (g:= (pi2 (ggen (N 0)))) (x:= (rr (N 2)))(y:= (rr (N 1))). reflexivity.
pose proof(EQBRmsg_msg'  (((((((EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x3) (grn 2)))  (m x2)  (m x2) (grn 1)   (exp (G 0) (m x2) (r 2))    (if_then_else_M
         (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) mx3rn1
         (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))
            (exp (G 0) (m x2) (r 2))
            (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))
               mx1rn1
               (if_then_else_M
                  ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x3) new))) &
                  (EQ_M (act x1) new) mx3rn1
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                       (EQ_M (to x2) (i 1))) & (notb (EQ_M (act x3) new))) &
                     (EQ_M (act x2) new) mx3rn2
                     (if_then_else_M
                        ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                          (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                        (EQ_M (act x1) new) mx2rn1
                        (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                           (if_then_else_M
                              (EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)
                              (grn 2) O))))))))).
simpl in H. rewrite H; clear.

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))) .
unfold mx3rn1.
pose proof(EQBRmsg_msg'   (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) (m x3) (m x3) (grn 2)  (exp (G 0) (m x3) (r 1)) 
   (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))
            (exp (G 0) (m x2) (r 2))
            (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))
               mx1rn1
               (if_then_else_M
                  ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x3) new))) &
                  (EQ_M (act x1) new) (exp (G 0) (m x3) (r 1))
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                       (EQ_M (to x2) (i 1))) & (notb (EQ_M (act x3) new))) &
                     (EQ_M (act x2) new) mx3rn2
                     (if_then_else_M
                        ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                          (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                        (EQ_M (act x1) new) mx2rn1
                        (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                           (if_then_else_M
                              (EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)
                              (grn 2) O)))))))).
simpl in H.
rewrite H; clear.
rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
reflexivity. 
rewrite H. reflexivity. 
rewrite H. 

assert(qc101_s # qd101_s) .
unfold qc101_s, qd101_s.
assert(qc201 # qd201).
unfold qc201, qd201.



 
rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2. 
pose proof(EQBRmsg_msg' (((((((EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x3) (grn 2)))  (m x2)  (m x2) (grn 1)   (exp (G 0) (m x2) (r 2))     (if_then_else_M
         (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) mx3rn1
         (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))
            (exp (G 0) (m x2) (r 2))
            (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))
               mx1rn1
               (if_then_else_M
                  ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x3) new))) &
                  (EQ_M (act x1) new) mx3rn1
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                       (EQ_M (to x2) (i 1))) & (notb (EQ_M (act x3) new))) &
                     (EQ_M (act x2) new) mx3rn2
                     (if_then_else_M
                        ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                          (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                        (EQ_M (act x1) new) mx2rn1
                        (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                           (if_then_else_M
                              (EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)
                              (grn 2) O))))))))).
simpl in H0. rewrite H0; clear.

rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))) .
unfold mx3rn1.
pose proof(EQBRmsg_msg'       (((((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 1))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) (m x3) (m x3) (grn 2)  (exp (G 0) (m x3) (r 1)) 
    (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))
            (exp (G 0) (m x2) (r 2))
            (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))
               mx1rn1
               (if_then_else_M
                  ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                    (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x3) new))) &
                  (EQ_M (act x1) new) (exp (G 0) (m x3) (r 1))
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x3) (i 1))) &
                       (EQ_M (to x2) (i 1))) & (notb (EQ_M (act x3) new))) &
                     (EQ_M (act x2) new) mx3rn2
                     (if_then_else_M
                        ((((EQ_M (reveal x4) (i 1)) & (EQ_M (to x2) (i 1))) &
                          (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
                        (EQ_M (act x1) new) mx2rn1
                        (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                           (if_then_else_M
                              (EQ_M (to x4) (i 2)) & (EQ_M (act x4) new)
                              (grn 2) O)))))))).
simpl in H.
rewrite H; clear.
rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
reflexivity. 
rewrite H0. reflexivity. 
rewrite H0.
reflexivity. rewrite H.
(********************************************************************************)
assert( qc010_ss #  qd010_ss).
unfold qc010_ss, qd010_ss.
assert(qc020_s # qd020_s).
unfold qc020_s, qd020_s.
assert(qc021 # qd021).
unfold qc021, qd021.





 
rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2. 
pose proof(EQBRmsg_msg' (((((((EQ_M (reveal x4) (i 3)) & (EQ_M (to x3) (i 2))) &
           (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 2))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x3) (grn 2)))  (m x2)  (m x2) (grn 1)   (exp (G 0) (m x2) (r 2))     (if_then_else_M
         (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 2))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2)) mx3rn1
         (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))
            (exp (G 0) (m x2) (r 2))
            (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))
               mx1rn1
               (if_then_else_M
                  ((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
                    (EQ_M (to x1) (i 2))) & (notb (EQ_M (act x3) new))) &
                  (EQ_M (act x1) new) mx3rn1
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2))) &
                       (EQ_M (to x1) (i 2))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1
                     (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                        (if_then_else_M
                           (EQ_M (to x4) (i 1)) & (EQ_M (act x4) new) 
                           (grn 1) O)))))))).

simpl in H0. rewrite H0; clear.


rewrite andB_comm with (b1:=   (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 2))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))) .
unfold mx3rn1.
pose proof(EQBRmsg_msg'      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
              (EQ_M (to x2) (i 3))) & (EQ_M (to x1) (i 2))) &
            (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
          (EQ_M (m x2) (grn 1))) (m x3) (m x3) (grn 2)  (exp (G 0) (m x3) (r 1)) 
    (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x2) (i 3))
            (exp (G 0) (m x2) (r 2))
            (if_then_else_M (EQ_M (reveal x4) (i 3)) & (EQ_M (to x1) (i 3))
               mx1rn1
               (if_then_else_M
                  ((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 2))) &
                    (EQ_M (to x1) (i 2))) & (notb (EQ_M (act x3) new))) &
                  (EQ_M (act x1) new) (exp (G 0) (m x3) (r 1))
                  (if_then_else_M
                     ((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x2) (i 2))) &
                       (EQ_M (to x1) (i 2))) & (notb (EQ_M (act x2) new))) &
                     (EQ_M (act x1) new) mx2rn1
                     (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                        (if_then_else_M
                           (EQ_M (to x4) (i 1)) & (EQ_M (act x4) new) 
                           (grn 1) O))))))).
simpl in H.
rewrite H; clear.
rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
reflexivity. 
rewrite H0. reflexivity. 
rewrite H0.
reflexivity. rewrite H0.

 reflexivity.
apply EQM in H. rewrite H. reflexivity.
Qed.