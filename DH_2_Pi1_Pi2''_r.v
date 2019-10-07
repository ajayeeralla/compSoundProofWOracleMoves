Load "tact_DH_2".

  
  
 

Theorem Pi1_Pi2'': phi4 ~ phi34.
Proof.
unfold phi4, phi34.

  repeat unf_phi. 
simpl. 
  
assert(H: (ostomsg t15) # (ostomsg t35)).
simpl.
 
 repeat unf.
Ltac make_false n := 
match goal with 
| [|- (if_then_else_M (EQ_M ?X (i ?N)) ?X1 ?Y1) #  (if_then_else_M (EQ_M ?X (i ?N)) ?X2 ?Y2) ] => assert (beq_nat N n =false) ; try reflexivity ;
match goal with 
| [H: beq_nat ?N ?N2 = false |- _ ] => 
  apply IFEVAL_M''' with (x:= X ) (n1:= N) (n2:= N2) (t1 := X1) (t2:= Y1) in H; rewrite H; clear H end
end.
repeat rewrite andB_elm'' with (b1:= (EQ_M (to x1) (i 1)) ) (b2:= (EQ_M (act x1) new)  ).
 false_to_sesns_all; simpl. 
repeat redg; repeat rewrite IFTFb.
aply_breq.
 repeat redg;  repeat rewrite IFTFb. 
aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
 repeat redg;  repeat rewrite IFTFb.
aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
  repeat redg;  repeat rewrite IFTFb.
aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
  repeat redg;  repeat rewrite IFTFb.
 aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
repeat aply_andB_elm.
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
 aply_breq.  
 repeat redg;  repeat rewrite IFTFb. reflexivity. 
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
 aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
aply_breq.  
 repeat redg;  repeat rewrite IFTFb. reflexivity. 
false_to_sesns_all; simpl. 
 repeat redg;  repeat rewrite IFTFb.
aply_breq.  
apply eqm in H. rewrite H. reflexivity. 

Qed.
 