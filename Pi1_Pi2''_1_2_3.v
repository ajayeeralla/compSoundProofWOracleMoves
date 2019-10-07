Load "tactics".

Axiom simpl_ifmorph: forall (n1 n2:nat) (m1 m2 m3: message), (if_then_else_M (Bvar n1) m1 (if_then_else_M  (Bvar n2) m2 m3)) # (if_then_else_M (Bvar n1) ((n1:= TRue)m1) (if_then_else_M  (Bvar n2) ((n1:=FAlse) (n2:= TRue) m2)  ((n1:=FAlse) (n2:= FAlse) m3) )).

Theorem RRS1: (phi1) ~ (phi31).

Proof.
  repeat unf. simpl.




pose proof(mor_eval_andB 1  grn1 (if_then_else_M (Bvar 1) grn1
               (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 2) 
                  grn1 (if_then_else_M (EQ_M (to x1) (i 2)) grn1 O))  )).
simpl in H. repeat red_in H. 

apply Forall_ELM_EVAL_M with (n:=1) (x:=(EQ_M (to x1) (i 1) )) in H.
 simpl in H.
apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (act x1) new)) in H.
 simpl in H.
rewrite H. clear H.
pose proof(mor_eval_andB 1  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r (N 1)))
              (if_then_else_M (Bvar 1)
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r (N 1))) O)).
simpl in H. repeat red_in H. 
apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x1) (i 2))) in H.
 simpl in H.
apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (act x1) new)) in H.
 simpl in H.
rewrite H. reflexivity. 
Qed.



Theorem RRS2: phi2 ~ phi32.

Proof.
  
(********t3************)
repeat unf.

pose proof(mor_eval_andB 1  grn1 (if_then_else_M (Bvar 1) grn1
               (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 2) 
                  grn1 (if_then_else_M (EQ_M (to x1) (i 2)) grn1 O))  )).
simpl in H. repeat red_in H. 

apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x1) (i 1))) in H.
 simpl in H.
apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (act x1) new)) in H.
 simpl in H.
rewrite H. clear H.
pose proof(mor_eval_andB 1  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r (N 1)))
              (if_then_else_M (Bvar 1)
                 (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r (N 1))) O)).
simpl in H. repeat red_in H. 
apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x1) (i 2))) in H.
 simpl in H.
apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (act x1) new)) in H.
 simpl in H.
rewrite H. 

simpl. clear H.
                                    


(***************t4***********************)


pose proof(mor_eval_andB 1  (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                  (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                     (if_then_else_M (EQ_M (to x2) (i 1)) acc
                        (if_then_else_M (EQ_M (to x2) (i 2)) grn2 O))))
               (if_then_else_M(Bvar 1)
                  (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                     (if_then_else_M
                        (EQ_M (reveal x2) (i 1)) &(Bvar 1)
                        mx1rn1
                        (if_then_else_M
                           (EQ_M (to x2) (i 2)) & (EQ_M (act x2) new) grn2 O)))
                  (if_then_else_M (EQ_M (to x1) (i 2)) &(Bvar 2)
                     (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                        (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                           (if_then_else_M (EQ_M (to x2) (i 2)) acc
                              (if_then_else_M (EQ_M (to x2) (i 1)) grn2 O))))
                     (if_then_else_M (EQ_M (to x1) (i 2))
                        (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                           (if_then_else_M
                              (EQ_M (reveal x2) (i 2)) & (EQ_M (to x1) (i 2))
                              mx1rn1
                              (if_then_else_M
                                 (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                 grn2 O))) O)))). simpl in H.
repeat red_in H.  rew_IFTF_all_in H .
 fall_elm_in 1  (EQ_M (to x1) (i 1)) H.
 fall_elm_in 2  (EQ_M (act x2) new) H. red_in H. 

reflexivity.
Qed.



Theorem RRS3 : phi3 ~ phi33.

Proof.
  
repeat unfold phi3, phi33, phi2, phi1, phi31, phi32, phi0. repeat unfold t10, t11, t12, t13,t14. simpl.
unfold qa0000.

pose proof(mor_eval_andB 1  grn1   (if_then_else_M (Bvar 1) grn1
                  (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 2)
                     grn1 (if_then_else_M (EQ_M (to x1) (i 2)) grn1 O)))).
apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x1) (i 1))) in H.
 simpl in H.

rewrite IFTRUE_M in H.
rewrite IFFALSE_M in H.
apply Forall_ELM_EVAL_M with (n:=2) (x:=  (EQ_M (act x1) new)) in H.
 simpl in H.
rewrite (IFSAME_M _ (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r (N 1)))) in H.
rewrite H .

pose proof(mor_eval_andB 1    (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r (N 1)))  (if_then_else_M (Bvar 1)
                     (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r (N 1))) O)).
simpl in H0.

rewrite IFTRUE_M in H0.

rewrite IFFALSE_M in H0.

rewrite IFSAME_M with (x:= (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0))) (r (N 1)))) in H0.

apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x1) (i 2))) in H0.
 simpl in H0.

apply Forall_ELM_EVAL_M with (n:=2) (x:=   (EQ_M (act x1) new)) in H0.
 simpl in H0.

rewrite H0 .
clear H. clear H0.

unfold qa1000, qa0010, qa0100, qa0001.
(**********(EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)**********)
pose proof (mor_eval_andB 1  (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                 (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                    (if_then_else_M (EQ_M (to x2) (i 1)) acc
                       (if_then_else_M (EQ_M (to x2) (i 2)) grn2 O)))) 
(if_then_else_M (Bvar 1)
                  (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                     (if_then_else_M
                        (EQ_M (reveal x2) (i 1)) & (Bvar 1)
                        mx1rn1
                        (if_then_else_M
                           (EQ_M (to x2) (i 2)) & (EQ_M (act x2) new) grn2 O)))
                  (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 2)
                     (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                        (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                           (if_then_else_M (EQ_M (to x2) (i 2)) acc
                              (if_then_else_M (EQ_M (to x2) (i 1)) grn2 O))))
                     (if_then_else_M (EQ_M (to x1) (i 2))
                        (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                           (if_then_else_M
                              (EQ_M (reveal x2) (i 2)) & (EQ_M (to x1) (i 2))
                              mx1rn1
                              (if_then_else_M
                                 (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                 grn2 O))) O)))).

simpl in H. rewrite IFTRUE_M in H. rewrite IFFALSE_M in H. 
pose proof(IFTF 3).

apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (reveal (f mphi1)) (i 1)) ) in H0. simpl in H0.
rewrite H0 in H.
apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x1) (i 1))) in H.
 simpl in H.

apply Forall_ELM_EVAL_M with (n:=2) (x:=   (EQ_M (act x1) new)) in H.
 simpl in H.

rewrite H.

(**********(EQ_M (to x1) (i 2)) & (EQ_M (act x1) new)**********)
pose proof (mor_eval_andB 1  (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                        (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                           (if_then_else_M (EQ_M (to x2) (i 2)) acc
                              (if_then_else_M (EQ_M (to x2) (i 1)) grn2 O))))
(if_then_else_M (Bvar 1)
                        (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                           (if_then_else_M
                              (EQ_M (reveal x2) (i 2)) & (Bvar 1)
                              mx1rn1
                              (if_then_else_M
                                 (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                 grn2 O))) O)).

simpl in H1. rewrite IFTRUE_M in H1.
 rewrite IFFALSE_M in H1.  
pose proof(IFTF 3).

apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (reveal (f mphi1)) (i 2)) ) in H2. simpl in H2.
rewrite H2 in H1.
clear H2.
clear H0.
apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x1) (i 2))) in H1.
 simpl in H1.

apply Forall_ELM_EVAL_M with (n:=2) (x:=   (EQ_M (act x1) new)) in H1.
 simpl in H1.




rewrite H1.
clear H. clear H1.
(**************************************)
(*********** (EQ_M (to (f mphi1)) (i 2)) &   (EQ_M (act (f mphi1)) new)*****)

pose proof (mor_eval_andB 1  (exp (pi1 (ggen (N 0))) (pi2 (ggen (N 0)))
                             (r (N 2))) O).

simpl in H.

apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x2) (i 2))) in H.
 simpl in H.

apply Forall_ELM_EVAL_M with (n:=2) (x:=   (EQ_M (act x2) new)) in H.
 simpl in H.
rewrite H.
clear H.

(***********************(EQ_M (to (f mphi1)) (i 1))
                                (EQ_M (act (f mphi1)) new) ***************)

pose proof (mor_eval_andB 1  (exp (pi1 (ggen (N 0))) 
                                (pi2 (ggen (N 0))) 
                                (r (N 2))) O).

simpl in H.

apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x2) (i 1))) in H.
 simpl in H.

apply Forall_ELM_EVAL_M with (n:=2) (x:=   (EQ_M (act x2) new)) in H.
 simpl in H.
rewrite H.
clear H.
(***********************************************************************)
(***********************************************************************)

unfold qa1000_s, qa0010_s, qa0100_s, qa0001_s.

unfold qa2000, qa1001, qa0020, qa0110, qa0200, qa0002.


(********************(EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)************)
(**************************************************************************)
pose proof (mor_eval_andB 1  (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                 (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                    (if_then_else_M (EQ_M (to x2) (i 1))
                       (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                          (if_then_else_M
                             ((((EQ_M (reveal x3) (i 1)) &
                                (EQ_M (to x2) (i 1))) & 
                               (Bvar 1)) &
                              (notb (EQ_M (act x2) new))) &
                             (Bvar 2) mx2rn1
                             (if_then_else_M
                                (EQ_M (to x3) (i 2)) & (EQ_M (act x3) new)
                                grn3
                                (if_then_else_M (EQ_M (to x3) (i 2)) grn3 O))))
                       (if_then_else_M (EQ_M (to x2) (i 2))
                          (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                             (if_then_else_M
                                (EQ_M (reveal x3) (i 2)) &
                                (EQ_M (to x1) (i 2)) mx1rn1
                                (if_then_else_M
                                   (EQ_M (reveal x3) (i 2)) &
                                   (EQ_M (to x2) (i 2)) mx2rn2
                                   (if_then_else_M (EQ_M (to x3) (i 1)) acc O))))
                          O)))) 


 (if_then_else_M (Bvar 1)  (if_then_else_M (EQ_M (reveal x2) (i 2)) O  (if_then_else_M  (EQ_M (reveal x2) (i 1)) & (Bvar 1)  (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                          (if_then_else_M (EQ_M (to x3) (i 2)) & (EQ_M (act x3) new) grn3 (if_then_else_M (EQ_M (to x3) (i 2)) grn3 O))) (if_then_else_M (EQ_M (to x2) (i 2)) & (EQ_M (act x2) new) (if_then_else_M (EQ_M (reveal x3) (i 2)) O (if_then_else_M (EQ_M (reveal x3) (i 1)) & (Bvar 1) mx1rn1 (if_then_else_M (EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1)) mx2rn2
                                   (if_then_else_M (EQ_M (to x3) (i 2)) acc O))))   O)))    (if_then_else_M (EQ_M (to x1) (i 2)) & (Bvar 2)  (if_then_else_M (EQ_M (reveal x2) (i 1)) O     (if_then_else_M (EQ_M (reveal x2) (i 2)) O   (if_then_else_M (EQ_M (to x2) (i 2)) (if_then_else_M (EQ_M (reveal x3) (i 1)) O (if_then_else_M ((((EQ_M (reveal x3) (i 2)) &
                                      (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 2))) &     (notb (EQ_M (act x2) new))) &
                                   (Bvar 2) mx2rn1
                                   (if_then_else_M
                                      (EQ_M (to x3) (i 1)) &
                                      (EQ_M (act x3) new) grn3
                                      (if_then_else_M 
                                         (EQ_M (to x3) (i 1)) grn3 O))))
                             (if_then_else_M (EQ_M (to x2) (i 1))
                                (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                                   (if_then_else_M
                                      (EQ_M (reveal x3) (i 1)) &
                                      (Bvar 1) mx1rn1
                                      (if_then_else_M
                                         (EQ_M (reveal x3) (i 1)) &
                                         (EQ_M (to x2) (i 1)) mx2rn2
                                         (if_then_else_M 
                                            (EQ_M (to x3) (i 2)) acc O)))) O))))
                    (if_then_else_M (EQ_M (to x1) (i 2))
                       (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                          (if_then_else_M
                             (EQ_M (reveal x2) (i 2)) & (EQ_M (to x1) (i 2))
                             (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                (if_then_else_M
                                   (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                                   grn3
                                   (if_then_else_M 
                                      (EQ_M (to x3) (i 1)) grn3 O)))
                             (if_then_else_M
                                (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                                (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                                   (if_then_else_M
                                      (EQ_M (reveal x3) (i 2)) &
                                      (EQ_M (to x1) (i 2)) mx1rn1
                                      (if_then_else_M
                                         (EQ_M (reveal x3) (i 2)) &
                                         (EQ_M (to x2) (i 2)) mx2rn2
                                         (if_then_else_M 
                                            (EQ_M (to x3) (i 1)) acc O)))) O)))
                       O)))).
simpl in H.

rewrite IFTRUE_M in H.
rewrite IFFALSE_M in H.
pose proof(IFTF 3).

apply Forall_ELM_EVAL_B with (n:=3) (b:=  (if_then_else_B
                                         (EQ_M (reveal (f mphi2)) (i 1))
                                         (EQ_M (to (f mphi1)) (i 1)) FAlse)) in H0. simpl in H0. 
rewrite H0 in H. clear H0.
pose proof(IFTF 3).

apply Forall_ELM_EVAL_B with (n:=3) (b:=   (if_then_else_B
                                   (if_then_else_B
                                      (EQ_M (reveal (f mphi2)) (i 1))
                                      (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                   (if_then_else_B 
                                      (EQ_M (act (f mphi1)) new) FAlse TRue)
                                   FAlse)) in H0. simpl in H0. 
rewrite H0 in H.

clear H0. 
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (EQ_M (reveal (f mphi1)) (i 1))) in H0. simpl in H0. 
rewrite H0 in H. clear H0.

pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=  (EQ_M (reveal (f mphi2)) (i 1))) in H0. simpl in H0. 
rewrite H0 in H. clear H0.

(*pose proof(Example16_B 3 TRue FAlse).

apply Forall_ELM_EVAL_B with (n:=3) (b:= (EQ_M (act (f mphi1)) new) ) in H0. simpl in H0. 
rewrite <- H0 in H. clear H0.*)

rewrite IFSAME_B in H.
apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to x1) (i 1))) in H.
 simpl in H.

apply Forall_ELM_EVAL_M with (n:=2) (x:=   (EQ_M (act x1) new)) in H.
simpl in H.

(*****************************  (EQ_M (to (f mphi2)) (i 2))
                                  (EQ_M (act (f mphi2)) new) **************)

pose proof (mor_eval_andB 1   (exp (pi1 (ggen (N 0))) 
                                   (pi2 (ggen (N 0))) 
                                   (r (N 3))) (if_then_else_M (Bvar 1)
                                   (exp (pi1 (ggen (N 0))) 
                                      (pi2 (ggen (N 0))) 
                                      (r (N 3))) O)).

simpl in H0. rewrite IFTRUE_M in H0. rewrite IFFALSE_M in H0. rewrite IFSAME_M in H0. 

apply Forall_ELM_EVAL_M with (n:=1) (x:=   (EQ_M (to (f mphi2)) (i 2))) in H0.
 simpl in H0.

apply Forall_ELM_EVAL_M with (n:=2) (x:=    (EQ_M (act (f mphi2)) new)) in H0.
 simpl in H0.
rewrite H0 in H.
clear H0.
simpl in H.

(******************************** (EQ_M (reveal (f mphi2)) (i 2))
                                   (EQ_M (to (f mphi0)) (i 2)))******************

pose proof (mor_eval_andB 1    (exp (pi1 (ggen (N 0))) 
                                   (m (f mphi0)) (r (N 1)))
                                  (if_then_else_M
                                   (if_then_else_B
                                      (Bvar 1)
                                      (EQ_M (to (f mphi1)) (i 2)) FAlse)
                                   (exp (pi1 (ggen (N 0))) 
                                      (m (f mphi1)) 
                                      (r (N 2)))  (if_then_else_M
                                      (EQ_M (to (f mphi2)) (i 1)) acc O))).

simpl in H0. rewrite IFTRUE_B in H0. rewrite IFFALSE_B in H0. rewrite IFFALSE_M in H0. 

apply Forall_ELM_EVAL_M with (n:=1) (x:=   (EQ_M (to (f mphi2)) (i 2))) in H0.
 simpl in H0.

apply Forall_ELM_EVAL_M with (n:=2) (x:=    (EQ_M (to (f mphi0)) (i 2))) in H0.
 simpl in H0.
***)


(***************(EQ_M (to (f mphi0)) (i 2)) 
                 (EQ_M (act x1) new)************************)



pose proof (mor_eval_andB 1  (if_then_else_M (EQ_M (reveal (f mphi1)) (i 1)) O
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
                                   FAlse) (Bvar 2) FAlse)
                             (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 1)))
                             (if_then_else_M
                                (if_then_else_B (EQ_M (to (f mphi2)) (i 1))
                                   (EQ_M (act (f mphi2)) new) FAlse)
                                (exp (pi1 (ggen (N 0))) 
                                   (pi2 (ggen (N 0))) 
                                   (r (N 3)))
                                (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                                   (exp (pi1 (ggen (N 0))) 
                                      (pi2 (ggen (N 0))) 
                                      (r (N 3))) O))))
                       (if_then_else_M (EQ_M (to (f mphi1)) (i 1))
                          (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2)) O
                             (if_then_else_M FAlse
                                (exp (pi1 (ggen (N 0))) 
                                   (m (f mphi0)) (r (N 1)))
                                (if_then_else_M
                                   (if_then_else_B
                                      (EQ_M (reveal (f mphi2)) (i 1))
                                      (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                   (exp (pi1 (ggen (N 0))) 
                                      (m (f mphi1)) 
                                      (r (N 2)))
                                   (if_then_else_M
                                      (EQ_M (to (f mphi2)) (i 2)) acc O)))) O))))


 (if_then_else_M (Bvar 1)
                 (if_then_else_M (EQ_M (reveal (f mphi1)) (i 1)) O
                    (if_then_else_M
                       (if_then_else_B (EQ_M (reveal (f mphi1)) (i 2))
                          (Bvar 1) FAlse)
                       (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1)) O
                          (if_then_else_M
                             (if_then_else_B (EQ_M (to (f mphi2)) (i 1))
                                (EQ_M (act (f mphi2)) new) FAlse)
                             (exp (pi1 (ggen (N 0))) 
                                (pi2 (ggen (N 0))) 
                                (r (N 3)))
                             (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                                (exp (pi1 (ggen (N 0))) 
                                   (pi2 (ggen (N 0))) 
                                   (r (N 3))) O)))
                       (if_then_else_M
                          (if_then_else_B (EQ_M (to (f mphi1)) (i 1))
                             (EQ_M (act (f mphi1)) new) FAlse)
                          (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1)) O
                             (if_then_else_M
                                (if_then_else_B
                                   (EQ_M (reveal (f mphi2)) (i 2))
                                   (Bvar 1) FAlse)
                                (exp (pi1 (ggen (N 0))) 
                                   (m (f mphi0)) (r (N 1)))
                                (if_then_else_M
                                   (if_then_else_B
                                      (EQ_M (reveal (f mphi2)) (i 2))
                                      (EQ_M (to (f mphi1)) (i 2)) FAlse)
                                   (exp (pi1 (ggen (N 0))) 
                                      (m (f mphi1)) 
                                      (r (N 2)))
                                   (if_then_else_M
                                      (EQ_M (to (f mphi2)) (i 1)) acc O)))) O)))
                 O)).
simpl in H0.


repeat (try rewrite IFTRUE_M in H0; try rewrite IFFALSE_M in H0; try rewrite IFSAME_M in H0;try rewrite IFTRUE_B in H0; try rewrite IFFALSE_B in H0; try rewrite IFSAME_B in H0).

apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to (f mphi0)) (i 2)) ) in H0.
 simpl in H0.

apply Forall_ELM_EVAL_M with (n:=2) (x:=    (EQ_M (act x1) new)) in H0.
 simpl in H0.

pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=   (if_then_else_B
                                          (EQ_M (reveal (f mphi2)) (i 2))
                                          (EQ_M (to (f mphi1)) (i 2)) FAlse)) in H1. simpl in H1. 
rewrite H1 in H0. clear H1.


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=    (if_then_else_B
                                    (if_then_else_B
                                       (EQ_M (reveal (f mphi2)) (i 2))
                                       (EQ_M (to (f mphi1)) (i 2)) FAlse)
                                    (if_then_else_B
                                       (EQ_M (act (f mphi1)) new) FAlse TRue)
                                    FAlse)) in H1. simpl in H1. 

rewrite H1 in H0. clear H1.


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=    (EQ_M (reveal (f mphi1)) (i 2))) in H1. simpl in H1. 
rewrite H1 in H0. clear H1.
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=    (EQ_M (reveal (f mphi2)) (i 2))) in H1. simpl in H1. 
rewrite H1 in H0. clear H1.


(********************(EQ_M (to (f mphi2)) (i 1))
                              (EQ_M (act (f mphi2)) new)**************)


pose proof (mor_eval_andB 1  (exp (pi1 (ggen (N 0))) 
                              (pi2 (ggen (N 0))) (r (N 3))) (if_then_else_M  (Bvar 1)
                              (exp (pi1 (ggen (N 0))) 
                                 (pi2 (ggen (N 0))) 
                                 (r (N 3))) O)).

simpl in H1. 

repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).

 apply Forall_ELM_EVAL_M with (n:=1) (x:=  (EQ_M (to (f mphi2)) (i 1)) ) in H1.
 simpl in H1.

apply Forall_ELM_EVAL_M with (n:=2) (x:=    (EQ_M (act (f mphi2)) new)) in H1.
 simpl in H1.

rewrite H1 in H0. clear H1.

(*************************************(EQ_M (reveal (f mphi2)) (i 2))****************************************)


pose proof(IFEVAL_M  (exp (pi1 (ggen (N 0))) (m (f mphi0)) (r (N 1)))
                              (if_then_else_M
                                 (if_then_else_B
                                    (Bvar 0)
                                    (EQ_M (to (f mphi1)) (i 2)) FAlse)
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi1)) (r (N 2)))
                                 (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                                    acc O)) 0).

apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (reveal (f mphi2)) (i 2))   ) in H1. simpl in H1.
repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
rewrite H1 in H0. clear H1.


(***************************(EQ_M (to (f mphi1)) (i 2))************)


pose proof(IFEVAL_M      (if_then_else_M (EQ_M (reveal (f mphi2)) (i 1)) O
                           (if_then_else_M
                              (if_then_else_B
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi2)) (i 2))
                                   (Bvar 0) FAlse)
                                 (if_then_else_B (EQ_M (act (f mphi1)) new)
                                    FAlse TRue) FAlse)
                              (exp (pi1 (ggen (N 0))) (m (f mphi1)) (r (N 1)))
                              (if_then_else_M (EQ_M (to (f mphi2)) (i 1))
                                 (exp (pi1 (ggen (N 0))) 
                                    (pi2 (ggen (N 0))) 
                                    (r (N 3))) O)))
                        (if_then_else_M (EQ_M (to (f mphi1)) (i 1))
                           (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2)) O
                              (if_then_else_M
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi2)) (i 1))
                                    (EQ_M (to (f mphi1)) (i 1)) FAlse)
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi1)) (r (N 2)))
                                 (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
                                    acc O))) O)  0).

apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (to (f mphi1)) (i 2)) ) in H1. simpl in H1.
repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
rewrite H1 in H0. clear H1.


pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=   (EQ_M (reveal (f mphi2)) (i 2))) in H1. simpl in H1. 
rewrite H1 in H0. clear H1.


(***********************************************(EQ_M (to (f mphi1)) (i 1))******************************)
pose proof( IFEVAL_M (if_then_else_M (EQ_M (reveal (f mphi2)) (i 2)) O
                              (if_then_else_M
                                 (if_then_else_B
                                    (EQ_M (reveal (f mphi2)) (i 1))
                                   (Bvar 0) FAlse)
                                 (exp (pi1 (ggen (N 0))) 
                                    (m (f mphi1)) (r (N 2)))
                                 (if_then_else_M (EQ_M (to (f mphi2)) (i 2))
                                    acc O))) O 0 ).

apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (to (f mphi1)) (i 1)) ) in H1. simpl in H1.
repeat (try rewrite IFTRUE_M in H1; try rewrite IFFALSE_M in H1; try rewrite IFSAME_M in H1;try rewrite IFTRUE_B in H1; try rewrite IFFALSE_B in H1; try rewrite IFSAME_B in H1).
rewrite H1 in H0. clear H1.
pose proof(IFTF 3).
apply Forall_ELM_EVAL_B with (n:=3) (b:=   (EQ_M (reveal (f mphi2)) (i 1))) in H1. simpl in H1. 
rewrite H1 in H0. clear H1.

reflexivity.
Qed.



