(*Require Export IND_DEFINITIONS.*)
Load "IND_DEFINITIONS".

Fixpoint not_occurn_atdk_bool (n : nat )(t:Bool) : bool :=
 match t with 
| Bvar n' => if (beq_nat n' n) then false else true
| FAlse => true
| TRue => true
| EQ_B  b1 b2 =>  andb (not_occurn_atdk_bool n b1)  (not_occurn_atdk_bool n b2)
| EQ_M t1 t2 => andb (not_occurn_atdk_msg n t1) ( not_occurn_atdk_msg n t2)
| if_then_else_B t1 t2 t3 => andb ( not_occurn_atdk_bool n t1)  (andb (not_occurn_atdk_bool n t2)(not_occurn_atdk_bool n t3) )
| EQL t1 t2 => andb (not_occurn_atdk_msg n t1) ( not_occurn_atdk_msg n t2)
 end
with not_occurn_atdk_msg (n : nat )(t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => andb (not_occurn_atdk_bool n b3) (andb (not_occurn_atdk_msg n  t1)( not_occurn_atdk_msg n t2))
| (Mvar n') => if (beq_nat n' n) then false else true
| O => true
| N n'=> if (beq_nat n' n) then false else true
|new => true
| exp t1 t2 t3 => andb ( not_occurn_atdk_msg n t1) (andb ( not_occurn_atdk_msg n t2) (not_occurn_atdk_msg n t3))
| pair t1 t2 => andb( not_occurn_atdk_msg n t1) ( not_occurn_atdk_msg n t2)
| pi1 t1 => ( not_occurn_atdk_msg n t1)
| pi2 t1 => ( not_occurn_atdk_msg n t1)
| ggen t1 => ( not_occurn_atdk_msg n t1)
| act t1 => ( not_occurn_atdk_msg n t1)
|r n' => if (beq_nat n' n) then false else true
| m t1 => ( not_occurn_atdk_msg n t1)
|enc t1 t2 t3 =>  andb ( not_occurn_atdk_msg n t1) (andb ( not_occurn_atdk_msg n t2) ( not_occurn_atdk_msg n t3))
|dec t1 t2 => ( not_occurn_atdk_msg n t2)
| k t1 => (not_occurn_atdk_msg n t1)
| pk t1 => ( not_occurn_atdk_msg n t1)
| sk t1 => ( not_occurn_atdk_msg n t1)
| nonce t1 => (not_occurn_atdk_msg n t1)
end.
 
Eval compute in (not_occurn_atdk_msg 1 (m (dec (N 1) (N 1)))).

Definition not_occurn_atdk_oursum (n :nat) (t:oursum) : bool :=
match t with 
| msg t1 => (not_occurn_atdk_msg n t1 )
| bol t1 => (not_occurn_atdk_bool n t1 )
end.

Eval compute in (not_occurn_atdk_oursum 1 (msg (dec (N 1) O))).

Fixpoint not_occurn_atdk_mylist {m:nat} (n:nat) (ml:mylist m): bool :=

match ml with
| [] => true
| h :: t => (andb (not_occurn_atdk_oursum n h) (not_occurn_atdk_mylist n t))
end.

Eval compute in (not_occurn_atdk_mylist 1 [msg (dec (N 1) O)]).


Axiom Eq1:  forall (m:nat) (w : mylist m) (x:message), (add_elt_last_mylist  (bol (EQ_M x x)) w ) ~ (add_elt_last_mylist (bol TRue) w ).
Check [msg (N 1)].
Axiom encCCA1 : forall (n1 n2 n m  :nat)(u u1 u2:message)(v: mylist m), (Fresh [n1 ; n2] (v ++ [ msg u ; msg u1 ; msg u2 ; msg (pk (N n)) ;  msg (sk (N n))] ) = true) /\  (not_occurn_atdk_mylist n (v++ [ msg u ; msg u1 ; msg u2 ]) = true )->
(add_elt_last_mylist (msg (if_then_else_M (EQL u u1) (enc u (pk (N n)) (r n1)) u2))v) ~ (add_elt_last_mylist (msg (if_then_else_M (EQL u u1) (enc u1 (pk (N n)) (r n2)) u2)) v)  .

Axiom encKP: forall (n1 n2 n3 n4 :nat) (m:nat)(v: mylist m) (u:message), (Fresh [n1 ; n2] (v ++ [ msg u; msg (pk (N n3)) ; msg (sk (N n3)); msg (pk (N n4)) ; msg (sk (N n4))]) = true) /\ (not_occurn_atdk_mylist n3 (v++ [ msg u  ]) = true ) /\ (not_occurn_atdk_mylist n4 (v++ [ msg u  ]) = true )  ->
 (add_elt_last_mylist (msg (enc u (pk (N n3)) (r n1))) v) ~ (add_elt_last_mylist (msg (enc u (pk (N n4)) (r n2))) v).




Theorem comp_soundness: forall (n1 n2 n3: nat)(g: message -> message -> message -> message -> message), (msg (if_then_else_M (EQ_M (pi1  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) (nonce (N n1))) (pk (N n3)) (r 1))) (sk (N n3)))) (pk (N n1))) (if_then_else_M (EQL (pair (pi2  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) (nonce (N n1))) (pk (N n3)) (r 1))) (sk (N n3)))) (nonce (N 0))) (pair (nonce (N 0)) (nonce (N n3))))
(enc  (pair (pi2  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) (N n1)) (pk (N n3)) (r 1))) (sk (N n3)))) (nonce (N n3)) (pk (N n1)) (r 1)) (enc (pair (nonce 1)(nonce 1)) (pk (N n1)) (r 1)))
(enc (pair (nonce 1)(nonce 1)) (pk (N n1)) (r 1))))+++[msg (pk (N n1));msg (pk (N n2));msg (pk (N n3)); msg (enc (pair (pk (N n1)), N n1) (pk (N n3)) (r 1)) ] 
 ~ (msg (if_then_else_M (EQ_M (pi1  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) N n1) (pk (N n3)) (r 1))) (sk (N n3)))) (pk (N n2))) (if_then_else_M (EQL (pair (pi2  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) N n1) (pk (N n3)) (r 1)))) (sk (N n3))) (nonce (N n3))) (pair (nonce N n3) (nonce N n3)))
(enc  (pair (pi2  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n2)) (enc (pair (pk (N n1)) N n1) (pk (N n3)) (r 1))) (sk (N n3)))) (nonce n3)) (pk (N n1)) (r 1)) (enc (pair (nonce 1)(nonce 1)) (pk (N n1)) (r 1)))
(enc (pair (nonce 1)(nonce 1)) (pk (N n1)) (r 1)))) +++ [msg (pk (N n1));msg (pk (N n2));msg (pk (N n3)); msg (enc (pair (pk (N n1)), N n1) (pk (N n3)) (r 1)) ]).



Theorem comp_soundness: forall (n1 n2 n3: nat)(g: message -> message -> message -> message -> message), (msg (if_then_else_M (EQ_M (pi1  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) (nonce (N n1))) (pk (N n3)) (r 1))) (sk (N n3)))) (pk (N n1))) (if_then_else_M (EQL (pair (pi2  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) (nonce (N n1))) (pk (N n3)) (r 1))) (sk (N n3)))) (nonce (N 0))) (pair (nonce (N 0)) (nonce (N 0)))) (enc (pair (pi2  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) (nonce (N n1))) (pk (N n3)) (r 1))) (sk (N n3)))) (nonce (N 0))) (pk (N n3)) (r 1)) (enc 
 (nonce (N 0))) (pair (nonce (N 0)) (nonce (N n3))))
(enc  (pair (pi2  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) (N n1)) (pk (N n3)) (r 1))) (sk (N n3)))) (nonce (N n3)) (pk (N n1)) (r 1)) (enc (pair (nonce 1)(nonce 1)) (pk (N n1)) (r 1)))
(enc (pair (nonce 1)(nonce 1)) (pk (N n1)) (r 1))))+++[msg (pk (N n1));msg (pk (N n2));msg (pk (N n3)); msg (enc (pair (pk (N n1)), N n1) (pk (N n3)) (r 1)) ] 
 ~ (msg (if_then_else_M (EQ_M (pi1  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) N n1) (pk (N n3)) (r 1))) (sk (N n3)))) (pk (N n2))) (if_then_else_M (EQL (pair (pi2  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n3)) (enc (pair (pk (N n1)) N n1) (pk (N n3)) (r 1)))) (sk (N n3))) (nonce (N n3))) (pair (nonce N n3) (nonce N n3)))
(enc  (pair (pi2  (dec (g (pk (N n1)) (pk (N n2))  (pk (N n2)) (enc (pair (pk (N n1)) N n1) (pk (N n3)) (r 1))) (sk (N n3)))) (nonce n3)) (pk (N n1)) (r 1)) (enc (pair (nonce 1)(nonce 1)) (pk (N n1)) (r 1)))
(enc (pair (nonce 1)(nonce 1)) (pk (N n1)) (r 1)))) +++ [msg (pk (N n1));msg (pk (N n2));msg (pk (N n3)); msg (enc (pair (pk (N n1)), N n1) (pk (N n3)) (r 1)) ]).
