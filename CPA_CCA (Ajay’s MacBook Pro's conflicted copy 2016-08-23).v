Load "DH_AUTH".

(******dec of encryption is plaintext****)

Axiom dep_enc :  forall(n:nat) (x z :message), (dec (enc x (pk n) z) (sk n)) # x.


Notation "  l '[[' n ']]' " := ((var_free_mylist n l) = true) (at level 0).


(*********check if sk(n) occurs only at dec postion ******************)

(*********************In a term : message and Bool********)
Fixpoint  skn_in_dec_bol (n : nat )(t:Bool) : bool :=
 match t with 
| Bvar n' => true
| FAlse => true
| TRue => true
| EQ_B  b1 b2 =>  (andb ( skn_in_dec_bol n b1)  (skn_in_dec_bol n b2))
| EQ_M t1 t2 => andb (skn_in_dec_msg n t1) ( skn_in_dec_msg n t2)
| if_then_else_B t1 t2 t3 => andb ( skn_in_dec_bol n t1)  (andb (skn_in_dec_bol n t2)(skn_in_dec_bol n t3) )
| EQL t1 t2 => andb (skn_in_dec_msg n t1) ( skn_in_dec_msg n t2)
| ver t1 t2 t3 => (andb  (andb (skn_in_dec_msg n t1) (skn_in_dec_msg n t2)) (skn_in_dec_msg n t3))
 end
with skn_in_dec_msg (n : nat )(t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => andb (skn_in_dec_bol n b3) (andb ( skn_in_dec_msg n  t1)(skn_in_dec_msg n t2))
| (Mvar n') =>  if (beq_nat n' n) then false else true
| O => true
| acc => true
| N n'=> true
|new => true
| exp t1 t2 t3 => andb ( skn_in_dec_msg n t1) (andb (  skn_in_dec_msg  n t2) ( skn_in_dec_msg n t3))
| pair t1 t2 => andb (  skn_in_dec_msg n t1) (  skn_in_dec_msg n t2)
| pi1 t1 => (  skn_in_dec_msg n t1)
| pi2 t1 => match t1 with 
             | k t2 => match t2 with
                       | N n' => if (beq_nat n' n) then false else true
                       | _ => true
                         end
             | _ => true

               end

| ggen t1 => (  skn_in_dec_msg n t1)
| act t1 => (  skn_in_dec_msg n t1)
| rr n' =>  true
| rs t1 => ( skn_in_dec_msg n t1)
| L t1 => ( skn_in_dec_msg n t1)
| m t1 => ( skn_in_dec_msg n t1)
|enc t1 t2 t3 =>  andb (  skn_in_dec_msg n t1) (andb (  skn_in_dec_msg n t2) (  skn_in_dec_msg n t3))
|dec t1 t2 => match t2 with 
             | (pi2 (k (N n'))) => if (beq_nat n' n) then (andb true (skn_in_dec_msg n t1))  else true
             | t2' => (skn_in_dec_msg n t1)
              end
| k t1 => (skn_in_dec_msg n t1)
| nonce t1 => (skn_in_dec_msg n t1)
| to t1 => (skn_in_dec_msg n t1) 
| reveal t1 => ( skn_in_dec_msg n t1)
| sign t1 t2 => (andb ( skn_in_dec_msg n t1) ( skn_in_dec_msg n t2))
| i n' => true

| f  l => (@forallb message (skn_in_dec_msg n) l)

end.


(*******************************************)

Eval compute in skn_in_dec_msg 1 (k(N 1)).
Eval compute in skn_in_dec_msg 1 ((pi2(k (N 1)))  ).

Eval compute in skn_in_dec_msg 1 (r  2).
(*********In a term os*****************************)

Definition skn_in_dec_os (n:nat)(t:oursum): bool :=
match t with 
|bol b => skn_in_dec_bol n b 
|msg t => skn_in_dec_msg n t
end.

(**** In a message list: ilist message n********)

Fixpoint skn_in_dec_mlist {m:nat}(x:nat) (ml : ilist message m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (skn_in_dec_msg x h) (skn_in_dec_mlist x ml1))
end.

(*******In a Bool list:  ilist Bool n************)

Fixpoint skn_in_dec_blist {m:nat}(x:nat) (ml : ilist Bool m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (skn_in_dec_bol x h) (skn_in_dec_blist x ml1))
end.

(********In a mylist : mylist n********)

Fixpoint skn_in_dec_mylist {m:nat}(x:nat) (ml :  mylist m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (skn_in_dec_os x h) (skn_in_dec_mylist x ml1))
end.


(**********************************************)
(********************To check if a term sk(n) doesn't occur *********)

(*********************In a term : message and Bool********)
Fixpoint  notocc_skn_bol (n:nat) (t:Bool) : bool :=
 match t with 
| Bvar n' =>  true
| FAlse => true
| TRue => true
| EQ_B  b1 b2 =>  (andb ( notocc_skn_bol n b1)  (notocc_skn_bol n b2))
| EQ_M t1 t2 => andb (notocc_skn_msg n t1) ( notocc_skn_msg n t2)
| if_then_else_B t1 t2 t3 => andb ( notocc_skn_bol n t1)  (andb (notocc_skn_bol n t2)(notocc_skn_bol n t3) )
| EQL t1 t2 => andb (notocc_skn_msg n t1) ( notocc_skn_msg n t2)
| ver t1 t2 t3 => (andb  (andb (notocc_skn_msg n t1) (notocc_skn_msg n t2)) (notocc_skn_msg n t3))
 end
with notocc_skn_msg (n:nat) (t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => andb (notocc_skn_bol n b3) (andb ( notocc_skn_msg n  t1)(notocc_skn_msg n t2))
| (Mvar n') =>  true
| O => true
| acc => true
| N n'=> true
|new => true
| exp t1 t2 t3 => andb ( notocc_skn_msg n t1) (andb (  notocc_skn_msg  n t2) ( notocc_skn_msg n t3))
| pair t1 t2 => andb (  notocc_skn_msg n t1) (  notocc_skn_msg n t2)
| pi1 t1 => (  notocc_skn_msg n t1)
| pi2 t1 => match t1 with 
             | k (N n') => if (beq_nat n' n) then false else true
             | _ => true

               end

| ggen t1 => (  notocc_skn_msg n t1)
| act t1 => (  notocc_skn_msg n t1)
| rr n' => true
| rs t1 => ( notocc_skn_msg n t1)
| L t1 => ( notocc_skn_msg n t1)
| m t1 => ( notocc_skn_msg n t1)
|enc t1 t2 t3 =>  andb (  notocc_skn_msg n t1) (andb (  notocc_skn_msg n t2) (  notocc_skn_msg n t3))
|dec t1 t2 => andb (notocc_skn_msg n t1) (notocc_skn_msg n t2)
| k t1 => (notocc_skn_msg n t1)
(*
| pk t1 => ( notoccur_msg n t1)
| sk t1 => ( notoccur_msg n t1)
*)
| nonce t1 => (notocc_skn_msg n t1)
 | to t1 => (notocc_skn_msg n t1) 
| reveal t1 => ( notocc_skn_msg n t1)
| sign t1 t2 => (andb ( notocc_skn_msg n t1) ( notocc_skn_msg n t2))
| i n' => true

| f  l => (@forallb message (notocc_skn_msg n) l)

end.

(***********************************************)
(*******************************************)


Eval compute in notocc_skn_msg 1 ((pi2(k (N 2)))  ).


(*********In a term os*****************************)

Definition notocc_skn_os (n:nat)(t:oursum): bool :=
match t with 
|bol b => notocc_skn_bol n b 
|msg t => notocc_skn_msg n t
end.

(**** In a message list: ilist message n********)

Fixpoint notocc_skn_mlist {m:nat}(x:nat) (ml : ilist message m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (notocc_skn_msg x h) (notocc_skn_mlist x ml1))
end.

(*******In a Bool list:  ilist Bool n************)

Fixpoint notocc_skn_blist {m:nat}(x:nat) (ml : ilist Bool m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (notocc_skn_bol x h) (notocc_skn_blist x ml1))
end.

(********In a mylist : mylist n********)

Fixpoint notocc_skn_mylist {m:nat}(x:nat) (ml :  mylist m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (notocc_skn_os x h) (notocc_skn_mylist x ml1))
end.


(********************To check if a term dec(t , sk(n)) doesn't occur *********)


(*********************In a term : message and Bool********)
Fixpoint  notocc_dec_bol (n:nat) (t:message)(k:Bool) : bool :=
 match k with 
| Bvar n' =>  true
| FAlse => true
| TRue => true
| EQ_B  b1 b2 =>  (andb ( notocc_dec_bol n t b1)  (notocc_dec_bol n t b2))
| EQ_M t1 t2 => andb (notocc_dec_msg n t t1) ( notocc_dec_msg n t t2)
| if_then_else_B t1 t2 t3 => andb ( notocc_dec_bol n t t1)  (andb (notocc_dec_bol n t t2)(notocc_dec_bol n t t3) )
| EQL t1 t2 => andb (notocc_dec_msg n t t1) ( notocc_dec_msg n t t2)
| ver t1 t2 t3 => (andb  (andb (notocc_dec_msg n t t1) (notocc_dec_msg n t t2)) (notocc_dec_msg n t t3))
 end
with notocc_dec_msg (n:nat) (t:message) (k:message) : bool :=
 match k with 
| if_then_else_M b3 t1 t2 => andb (notocc_dec_bol n t b3) (andb ( notocc_dec_msg n t  t1)(notocc_dec_msg n t t2))
| (Mvar n') =>  true
| O => true
| acc => true
| N n'=> true
|new => true
| exp t1 t2 t3 => andb ( notocc_dec_msg n t t1) (andb (  notocc_dec_msg  n t t2) ( notocc_dec_msg n t t3))
| pair t1 t2 => andb (  notocc_dec_msg n t t1) (  notocc_dec_msg n t t2)
| pi1 t1 => (  notocc_dec_msg n t t1)
| pi2 t1 => (notocc_dec_msg n t t1)
| ggen t1 => (  notocc_dec_msg n t t1)
| act t1 => (  notocc_dec_msg n t t1)
| rr n' => true
| rs t1 => ( notocc_dec_msg n t t1)
| L t1 => ( notocc_dec_msg n t t1)
| m t1 => ( notocc_dec_msg n  t t1)
|enc t1 t2 t3 =>  andb (  notocc_dec_msg n t t1) (andb (  notocc_dec_msg n t t2) (  notocc_dec_msg n t t3))
|dec t1 t2 =>  match t1 , t2  with
              | t , pi2(k (N n')) => if (beq_nat n' n) then false else true
              | _ , _ => true
            
                   end
                           
| k t1 => (notocc_dec_msg n t t1)
(*
| pk t1 => ( notoccur_msg n t1)
| sk t1 => ( notoccur_msg n t1)
*)
| nonce t1 => (notocc_dec_msg n t t1)
 | to t1 => (notocc_dec_msg n t t1) 
| reveal t1 => ( notocc_dec_msg n t t1)
| sign t1 t2 => (andb ( notocc_dec_msg n t t1) ( notocc_dec_msg n t t2))
| i n' => true

| f  l => (@forallb message (notocc_dec_msg n t) l)

end.



(***********************************************)
(*******************************************)


Eval compute in notocc_dec_msg 1 O (dec _ (pi2 (k (N 1)))).

(*********In a term os*****************************)

Definition  notocc_dec_os (n:nat)(t:message)(k:oursum): bool :=
match k with 
|bol b => notocc_dec_bol n t b 
|msg t1 => notocc_dec_msg n t t1
end.

(**** In a message list: ilist message n********)

Fixpoint notocc_dec_mlist (x:nat) (t:message) (ml : list message):bool :=
match ml with
| nil  => true
| cons h tl => (andb (notocc_dec_msg x t h) (notocc_dec_mlist x  t tl ))
end.

(*******In a Bool list:  ilist Bool n************)

Fixpoint notocc_dec_blist (x:nat) (t:message)(ml : list Bool ):bool :=
match ml with
| nil => true
| cons h tl => (andb (notocc_dec_bol x t h) (notocc_dec_blist x t tl))
end.

(********In a mylist : mylist n********)

Fixpoint notocc_dec_mylist {m:nat}(x:nat)(t:message) (ml :  mylist m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (notocc_dec_os x t h) (notocc_dec_mylist x t ml1))
end.

(*******************************************************************************************************)
(***********Formula*************************************************************************************)
(****
Definition formula (u u' u'': message) (n n1 n2 n3 :nat){m} (l:mylist m) : Prop := (l [[ n ]]) /\ (clos_listm [u;u';u'']  = true)/\  ( onlyin_pkrsk_mylist n1  ( (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n2)) u'') l) ++ (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n3)) u'') l)) = true) /\  ( skn_in_dec_mylist n1 ((submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n2)) u'') l) ++ (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n3)) u'') l)) = true) /\ (notocclist_mylist [n2; n3]  ((submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n2)) u'') l) ++ (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u' (pk n1) (r n3)) u'') l)) = true)  -> (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n2)) u'') l) ~ 
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n3)) u'') l).
**)

(********************ENCCPA*******************************************)
(********************************************************************)

Axiom ENCCPA: forall (u u' u'': message) (n n1 n2 n3 :nat){m} (l:mylist m), ( (var_free_mylist n l) = true) /\ (clos_listm [u; u'; u''] = true) /\  (notocc_skn_mylist n1  ((submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n2)) u'') l) ++
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n3)) u'') l)) = true)  -> (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n2)) u'') l) ~
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n3)) u'') l).


(********************ENCCCA1*****************************************)
(********************************************************************)

Axiom ENCCCA1 : forall (t u u' u'': message) (n n1 n2 n3 :nat){m} (l :mylist m), (var_free_msg n t = true) /\ (var_free_mylist n l = true)  /\ (notocc_dec_mlist n1 t  (subterm_list_mylist  l ) = true) -> (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n2)) u'') l) ~
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n3)) u'') l).

 

(*********************ENCCA2***************************************)
(******************************************************************)


Axiom ENCCCA2: forall (t1 t2 u u' u'': message) (n n1 n2 n3 m :nat) (l:mylist m),  (var_free_mylist n ([msg t1; msg t2] ++ l) = true) /\  ((notocc_dec_mlist n1 t1  (subterm_list_mylist  l ) = false) ->  (dec t1 (sk n1)) # (if_then_else_M  ((EQ_M t1  (Mvar 2))& (EQ_M (L u) (L u'))) t2 (dec t1 (sk n1)))) -> 
 (submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n2)) u'') l) ~
(submsg_mylist n (if_then_else_M (EQ_M (L u) (L u')) (enc u (pk n1) (r n3)) u'') l).
(*****nonce and key generation ******)

Definition lnonce {n} := (L (N n)).
(**Definition lskey {n} := (L (sk n)).**)




(*******length regular********)

Axiom len_regular: forall (x1 x2 y1 y2 :message), (L x1) # (L y1) /\ (L x2) # (L y2) -> (L (pair x1 x2)) # (L (pair y1 y2)).

(******Idempotent L(L(x)) = L(x)**********)

Axiom idemp_L: forall x,  (L (L x)) # (L x).
Variable lskey : message.

Axiom lsk: forall n, lskey # (L (sk n)). 

(**************real or random secrecy of n****)





Theorem RRS_n: forall (n n' n1 n2 n3 n4 n5 n6 :nat), [ msg (enc (pair (sk  n1) (N n5)) (pk n2) (rs (N (n3)))); msg (enc (pair (pi2 (dec (f [ (enc (pair (sk  n1) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n)] ~
 [ msg (enc (pair (sk  n1) (N n5)) (pk n2) (rs (N (n3)))); msg (enc (pair (pi2 (dec (f [ (enc (pair (sk  n1) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))) (N n)) (pk n1) (rs (N n4))); msg (N n')].


Proof. intros.

assert(H: (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]) # (if_then_else_M (EQ_M (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))])  (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))) (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]) (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]))).
pose proof (IFSAME_M).
rewrite IFSAME_M with (b:=  (EQ_M (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))])  (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3)))))) (x:= (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))])). 
reflexivity.

assert (H1:  (pi2 (dec (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))) # (if_then_else_M  (EQ_M (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))])  (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))) (N n5)  (pi2 (dec (f [ (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3))))]) (sk n2))))).

rewrite H at 1.

pose proof(Example11_M).

apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))])) in H0. simpl in H0.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (enc (pair (sk n1) ( N n5 )) (pk n2) (rs (N n3))) ) in H0. simpl in H0.
apply  Forall_ELM_EVAL_M1 with (n:=3) (x :=  (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))])) in H0. simpl in H0.
 

rewrite H0 .


assert(H3:  (pi2 (dec (if_then_else_M (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk n2))) # (if_then_else_M (Bvar 0) (pi2 (dec (Mvar 1) (sk n2))) (pi2 (dec (Mvar 2) (sk n2))))).


rewrite <- IFSAME_M with (b:= (Bvar 0)) (x:=  (pi2 (dec (if_then_else_M (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk n2)))).

rewrite IFEVAL_M .
simpl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
reflexivity.
apply Forall_ELM_EVAL_M with (n:=0) (x:= (EQ_M (f [enc (pair (sk n1) (N n5)) (pk n2) (rs (N n3))]) (enc (pair (pi2 (k (N n1))) (N n5)) (pi1 (k (N n2))) (rs (N n3))))) in H3.
simpl in H3.
apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (enc (pair (pi2 (k (N n1))) (N n5)) (pi1 (k (N n2))) (rs (N n3)))) in H3. simpl in H3.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (f [enc (pair (sk n1)  (N n5)) (pk n2) (rs (N n3))])) in H3. simpl in H3.

rewrite H3.
pose proof(dep_enc).
rewrite dep_enc with (n:=n2) (x:=  (pair (pi2 (k (N n1))) (N n5 ))) .
rewrite proj2 with (m1:= (pi2 (k (N n1)))) (m2 := (N n5)) .
reflexivity.
(*************definition************)

(*
Definition l := [msg (Mvar 1) ; msg (enc (if_then_else_M (EQ_M (f [Mvar 1]) (Mvar 1) ) (N n5) (pi2 (dec (f [Mvar 1]) (sk n2)))) (pk n2) (rs (N 3)) ) ; msg (N 0)].*)
(**************L<sk1 , n5> , L<sk6, n5> *********)

assert(H2: (L (pair (sk n1) (N n5))) # (L (pair (sk n6) (N n5)))).

apply len_regular.  split.
Focus 2.
reflexivity.

assert(H3: lskey # ( L (sk n1))).
rewrite lsk with (n:= n1).

reflexivity.

assert(H4: lskey # ( L (sk  n6))).
rewrite lsk with (n:= n6).

reflexivity.

rewrite <- H3.
rewrite <- H4.
reflexivity.
apply EQmsg in H2.
pose proof (IFTRUE_M).
pose proof (IFTRUE_M  (enc (pair (sk n1) (N n5)) (pk n2) (rs (N (n3)))) O).
rewrite <- H2 in H3.

pose proof (IFTRUE_M  (enc (pair (sk n6) (N n5)) (pk n2) (rs (N (n3)))) O).
rewrite <- H2 in H4.

simpl.



pose proof (ENCCCA2 (f [Mvar 1]) (N n5) (pair (sk n1) (N n5)) (pair (sk n6) (N n5)) O 1 n2 n3 n3 3 [msg (Mvar 1) ; msg (enc (if_then_else_M (EQ_M (f [(Mvar 1)]) (Mvar 1)) (N n5) (pi2(dec (f [(Mvar 1)]) (sk n2)))) (r n3) (pk n2) ); msg (N n)]).
simpl in H5. 
Admitted.