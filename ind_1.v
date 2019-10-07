Load "IND_DEFINITIONS".

Theorem ind_name: forall n:nat,  (N 0) = O ->  ((N n) = O -> (N (k+1))=O) -> forall n, (N n) = O.
Proof. 
intros. 
induction n.  assumption. simpl. 
apply H0 with (k0:= n).
exists 0 . 
apply H0 with (k0:= 0) in H. 
rewrite  H0 with (k0 := 0) in H. 