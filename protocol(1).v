Load "CORE_AXIOMS".

(* check if secret key(given nat) occurs in any other position except decreption position *)
 
Fixpoint decoccur_bol (n : nat )(t:Bool) : bool :=
 match t with 
| Bvar n' => true
| FAlse => true
| TRue => true
| EQ_B  b1 b2 => true
| EQ_M t1 t2 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => (notoccur_msg n (N n''))
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => (andb (decoccur_msg n t1) (decoccur_msg n t2))
                  end 
| if_then_else_B t1 t2 t3 => andb (decoccur_bol n t1) (andb (decoccur_bol n t2) (decoccur_bol n t3))
| EQL t1 t2 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (andb (decoccur_msg n t1) (decoccur_msg n t2))
                  end
| ver t1 t2 t3 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => match (t3) with
                                                                                      |( (pi2 (k (N n''')))) => (notoccur_msg n (N n'''))
                                                                                      | _ => (notoccur_msg n (N n''))
                                                                                end
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => andb (decoccur_msg n t1) (andb (decoccur_msg n t2) (decoccur_msg n t3))
                  end 
end
with decoccur_msg (n : nat )(t:message) : bool :=
 match t with 
| (Mvar n') => true
| O => true
| acc => true
| N n'=> true
| if_then_else_M b3 t1 t2 => match (t1) with 
                                  | ( (pi2 (k (N n')))) => match (t2) with
                                                                  |( (pi2 (k (N n'')))) => (notoccur_msg n (N n''))
                                                                  | _ => (notoccur_msg n (N n'))
                                                           end
                                                      
                                  | _ => andb (decoccur_bol n b3) (andb (decoccur_msg n t1) (decoccur_msg n t2))
                             end 
| exp t1 t2 t3 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => match (t3) with
                                                                                      |( (pi2 (k (N n''')))) => (notoccur_msg n (N n'''))
                                                                                      | _ => (notoccur_msg n (N n''))
                                                                                end
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => andb (decoccur_msg n t1) (andb (decoccur_msg n t2) (decoccur_msg n t3))
                  end 

| pair t1 t2 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => (notoccur_msg n (N n''))
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => (andb (decoccur_msg n t1) (decoccur_msg n t2))
                  end 
| pi1 t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| pi2 t1 => match (t1) with 
                       | ( (k (N n'))) => (notoccur_msg n (N n'))
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| ggen t1 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| rr t1 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
|new => true
| act t1 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| m t1 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| nonce t1 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| enc t1 t2 t3 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => match (t3) with
                                                                                      |( (pi2 (k (N n''')))) => (notoccur_msg n (N n'''))
                                                                                      | _ => (notoccur_msg n (N n''))
                                                                                end
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => andb (decoccur_msg n t1) (andb (decoccur_msg n t2) (decoccur_msg n t3))
                  end 
| dec t1 t2 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| to t1 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| k t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
(*
| pk t1 => (decoccur_msg n t1)
| sk t1 => (notoccur_msg n t1) *)
| sign t1 t2 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => (notoccur_msg n (N n''))
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => (andb (decoccur_msg n t1) (decoccur_msg n t2))
                  end 
| reveal t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| i n' => true
| L t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| rs t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (decoccur_msg n t1)
                  end
| f  l =>  (@forallb message (decoccur_msg n) l)
 end.

Eval compute in (decoccur_msg 1 (dec (sk 1) (pk 1))).

(*** nat in term oursum ***)
Fixpoint decoccr_oursum (n:nat)(t:oursum): bool :=
match t with 
|bol t => decoccur_bol n t 
|msg t => decoccur_msg n t
end.
(**** message in ilist mesg ****)
Fixpoint decoccr_mlist {m:nat}(x: nat) (v : ilist message m):bool :=
match v with
| [] => true
| h :: v1 => (andb (decoccur_msg x h) (decoccr_mlist x v1))
end.

(**** message in mylist ****)
Fixpoint decoccr_mylist {m:nat}(x:nat) (v :  mylist m):bool :=
match v with
| [] => true
| h :: v1 => (andb (decoccr_oursum x h) (decoccr_mylist x v1))
end.

Eval compute in (decoccr_mylist 1 [msg (dec (N 1)(N 3))]).

(**** ilist nat in ilist ****)
Fixpoint decocclist_mlist {n:nat} {m:nat}(skl:ilist nat n)(v:ilist message m): bool :=
match skl with
|[] => true
| h::t=> (andb (decoccr_mlist h v) (decocclist_mlist t v))
end.

Eval compute in (decoccr_mlist 8 [dec (N 1) (N 1); dec (N 3) (r 4)]).

(***** ilist nat in mylist*****)

Fixpoint decocclist_mylist {n:nat} {m:nat}(sk:ilist nat n)(v: mylist m): bool :=
match sk with
|[] => true
| h::t=> (andb (decoccr_mylist h v) (decocclist_mylist t v))
end.

Eval compute in (decocclist_mlist [1] [k (sk 1)]).

Eval compute in (Fresh [1;3] [msg (dec (k (N 9)) (k (N 1))); msg (dec (k (N 2)) (k (N 2)))]).
Eval compute in (Fresh [6;8] [msg (pair (pi2 (dec (ggen (N 3)) (sk 2))) (N 1))]).



(* check if secret key(given nat) occurs in dec position *)

Fixpoint nodec_Bool (n : nat ) (t:Bool) : bool :=
 match t with 
| Bvar n' => true
| FAlse => true
| TRue => true
| EQ_B  b1 b2 => true
| EQ_M t1 t2 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => (notoccur_msg n (N n''))
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => andb (nodec_msg n t1) (nodec_msg n t2)
                  end 
| if_then_else_B t1 t2 t3 => andb (nodec_Bool n t1) (andb (nodec_Bool n t2) (nodec_Bool n t3))
| EQL t1 t2 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => (notoccur_msg n (N n''))
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => andb (nodec_msg n t1) (nodec_msg n t2)
                  end 
| ver t1 t2 t3 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => match (t3) with
                                                                                      |( (pi2 (k (N n''')))) => (notoccur_msg n (N n'''))
                                                                                      | _ => (notoccur_msg n (N n''))
                                                                                end
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => andb (nodec_msg n t1) (andb (nodec_msg n t2) (nodec_msg n t3))
                  end 
 end
with nodec_msg (n : nat ) (t:message) : bool := 
 match t with 
| if_then_else_M b3 t1 t2 => match (t1) with 
                             |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => (notoccur_msg n (N n''))
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                             | _ => andb (nodec_Bool n b3) (andb (nodec_msg n t1) (nodec_msg n t2))
                             end 
| (Mvar n') => true
| O => true
| acc => true
| N n'=> true
| rr t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
            end
|new => true
| exp t1 t2 t3 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => match (t3) with
                                                                                      |( (pi2 (k (N n''')))) => (notoccur_msg n (N n'''))
                                                                                      | _ => (notoccur_msg n (N n''))
                                                                                end
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => andb (nodec_msg n t1) (andb (nodec_msg n t2) (nodec_msg n t3))
                  end
| pair t1 t2 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => match (t2) with 
                                                      | ( (pi2 (k (N n'')))) => (notoccur_msg n (N n''))
                                                      | _ => (notoccur_msg n (N n'))
                                                 end
                       | _ => andb (nodec_msg n t1) (nodec_msg n t2)
                  end 
| dec t1 t2 =>  match (t2) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| enc t1 t2 t3 => andb (nodec_msg n t1) (andb (nodec_msg n t2) (nodec_msg n t3))
| k t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| to t1 => match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
            end
(*
| pk t1 => nodec_msg n t1
| sk t1 => notoccur_msg n t1 *)
| pi1 t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| pi2 t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| ggen t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| act t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| nonce t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| m t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| sign t1 t2 => andb (nodec_msg n t1) (nodec_msg n t2)
| reveal t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| i n' => true
| L t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| rs t1 =>  match (t1) with 
                       |  ( (pi2 (k (N n')))) => (notoccur_msg n (N n'))
                       | _ => (nodec_msg n t1)
                  end
| f  l => (@forallb message (nodec_msg n ) l)
 end.

Eval compute in (nodec_msg 1 (sk 1)).

(**** nat in oursum ***)
Fixpoint nodec_oursum (n:nat) (t:oursum) : bool :=
match t with 
|bol b => nodec_Bool n b 
|msg t => nodec_msg n t
end.


(**** message in ilist mesg ****)

Fixpoint nodec_mlist {m:nat} (x: nat) (v : ilist message m):bool :=
match v with
| [] => true
| h :: v1 => (andb (nodec_msg x h) (nodec_mlist x v1))
end.

(**** message in mylist ****)
Fixpoint nodec_mylist {m:nat} (x:nat) (v :  mylist m) :bool :=
match v with
| [] => true
| h :: v1 => (andb (nodec_oursum x h) (nodec_mylist x v1))
end.

Eval compute in (nodec_mylist 1[msg (dec (N 1)(N 3))]).

(**** ilist nat in ilist mesg  ****)
Fixpoint nodeclist_mlist {n:nat} {m:nat}(sk:ilist nat n) (v:ilist message m): bool :=
match sk with
|[] => true
| h::t=> (andb (nodec_mlist h v) (nodeclist_mlist t v))
end.

Eval compute in (nodec_mlist 8  [dec (N 1) (N 8); dec (N 3) (r 4)] ).
Eval compute in (nodeclist_mlist [1;3] [dec (N 5) (N 1); dec (N 2) (N 2)] ).
(*** ilist nat in mylist ***)

Fixpoint nodeclist_mylist {n:nat} {m:nat} (sk: ilist nat n) (v:mylist m): bool :=
match sk with
|[] => true
| h::t=> (andb (nodec_mylist h v) (nodeclist_mylist t v))
end.

Eval compute in (nodeclist_mlist [1;3] [dec (k (N 5)) (sk 9); dec (k (sk 3)) (pk 7)] ).
Eval compute in (decocclist_mylist [1] [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6)); msg (enc (pair (N 6) (N 6)) (r 4) (pk 1))]).
 
Axiom EncCCA1 : forall (x x' n m: nat) (u u' u'': message) (v: mylist n) , (Fresh [x ; x'] (v ++ [msg u; msg u'; msg u''; msg (pk m); msg (sk m)]) = true) /\ (decocclist_mylist [m] (v ++ [msg u; msg u'; msg u'']) = true) -> 
(v ++ [msg (if_then_else_M (EQL u u') (enc u (r x) (pk m)) u'') ]) ~ (v ++ [msg (if_then_else_M (EQL u u') (enc u' (r x') (pk m)) u'') ]).


Axiom EncKP : forall (n x x' m o: nat) (u : message) (v: mylist n) , ((Fresh [x ; x'] (v ++ [msg u; msg (pk m) ; msg (sk m) ; msg (pk o); msg (sk o)])) = true) /\ ((nodeclist_mylist [m ; o] (v ++ [msg u])) = true) /\ ((decocclist_mylist [m ; o] (v ++ [msg u])) = true) -> 
(v ++ [msg (enc u (r x) (pk m))]) ~ (v ++ [msg (enc u (r x') (pk o))]) .

Axiom if1 : forall (x y z : message) (b : Bool) (n : nat) (w : mylist n) , ((([bol b] ++ w) ++ [msg x]) ~ (([bol b] ++ w) ++ [msg z])) /\ ((([bol b] ++ w) ++ [msg y]) ~ (([bol b] ++ w) ++ [msg z])) -> (w ++ [msg (if_then_else_M b x y)]) ~ (w ++ [msg z]).



(***************** ([msg (N a); msg (N b); msg (N a'); msg (pk (k (N a))); msg (pk (k (N b))); msg (pk (k (N a'))); msg (enc ( pair (pk (k (N a'))) (N n)) (N p) (pk (k (N b))) ) ] ++ [msg (if_then_else_M (EQ_M (pi1 (dec (N phi0) (sk (k (N b))))) (pk (k (N a)))) (if_then_else_M (EQL (pair (pi2 (dec (N phi0) (sk (k (N b))))) (N n)) (pair (N n) (N n))) (enc (pair (pi2 (dec (N phi0) (sk (k (N b))))) (N n)) (N p) (pk (k (N a)))) (enc (pair (N n) (N n)) (N p) (pk (k (N a))))) (enc (pair (N n) (N n)) (N x) (pk (k (N a))))) ]) ~ ([msg (N a); msg (N b); msg (N a'); msg (pk (k (N a))); msg (pk (k (N b))); msg (pk (k (N a'))); msg (enc ( pair (pk (k (N a'))) (N n)) (N 0) (pk (k (N b))) ) ] ++ [msg ( if_then_else_M (EQ_M (pi1 (dec (N phi0) (sk (k (N b))))) (pk (k (N a')))) (if_then_else_M (EQL (pair (pi2 (dec (N phi0) (sk (k (N b))))) (N n)) (pair (N n) (N n))) (enc (pair (pi2 (dec (N phi0) (sk (k (N b))))) (N n)) (N q) (pk (k (N a')))) (enc (pair (N n) (N n)) (N q) (pk (k (N a'))))) (enc (pair (N n) (N n)) (N q) (pk (k (N a')))) )]) **********)
Eval compute in f [(r 4); (N 9)].
(******  For Phi 2 1 r=4, r'=5  *******   For Phi 2' 1 r=7, r'= 8    *****)
Theorem verification:([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (if_then_else_M (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1)) (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1); (N 2); (N 3); (pk 1); (pk 2);(pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 4) (pk 1)) (enc (pair (N 6) (N 6)) (r 100) (pk 1))) (enc (pair (N 6) (N 6)) (r 5) (pk 1))) ]) ~ ([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg ( if_then_else_M (EQ_M (pi1 (dec (f [(N 1);  (N 2); (N 3);(pk 1); (pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3)) (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1);  (N 2); (N 3); (pk 1); (pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 7) (pk 3)) (enc (pair (N 6) (N 6)) (r 100) (pk 3))) (enc (pair (N 6) (N 6)) (r 8) (pk 3)) )]) .
Proof.
intros.
simpl.
(*******************  phi 2 1 ************************)
assert (H1 : (Fresh [4;5] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1))] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6)); msg (enc (pair (N 6) (N 6)) (r 100) (pk 1)) ;msg (pk 1); msg (sk 1)]) = true) /\ (decocclist_mylist [1] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1))] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6));msg (enc (pair (N 6) (N 6)) (r 100) (pk 1))]) = true)).
split.
simpl.
reflexivity.
reflexivity.  
apply EncCCA1 in H1. 
assert (H2 : ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) /\ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (enc (pair (N 6) (N 6)) (r 100) (pk 1))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))])).
split.
reflexivity.
(******  EncKP is used to prove indistingishability for enc terms with different r **********)
apply EncKP with (v:= ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) ; bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )])) (u:=(pair (N 6) (N 6))) (x' := 5)(x := 100).
split.
simpl.
reflexivity.
split.
reflexivity.
reflexivity. 
apply if1 with (b:= EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (w:= ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )])) (x:=(enc (pair (N 6) (N 6)) (r 5) (pk 1))) (y:= (enc (pair (N 6) (N 6)) (r 100) (pk 1))) (z:= (enc (pair (N 6) (N 6)) (r 5) (pk 1)))in H2.
rewrite H2 in H1. 
(******** including phi0 term ***********)
assert (H3 : (Fresh [4;5] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1)) ; msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6)); msg (enc (pair (N 6) (N 6)) (r 100) (pk 1)) ;msg (pk 1); msg (sk 1)]) = true) /\ (decocclist_mylist [1] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1)); msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++  [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6));msg (enc (pair (N 6) (N 6)) (r 100) (pk 1))]) = true)).
split.
simpl.
reflexivity.
reflexivity. 
apply EncCCA1 in H3.
 assert (H4 : ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++  ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) /\ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 100) (pk 1))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))])).
split.
reflexivity.
apply EncKP with (v:= ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ])) (u:=(pair (N 6) (N 6))) (x' := 5)(x := 100).
split.
simpl.
reflexivity.
split.

reflexivity.
reflexivity.
apply if1 with (b := (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))) (w := ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ])) (x := (enc (pair (N 6) (N 6)) (r 5) (pk 1))) (y := (enc (pair (N 6) (N 6)) (r 100) (pk 1))) (z := (enc (pair (N 6) (N 6)) (r 5) (pk 1))) in H4.
rewrite H4 in H3.
assert (H5 : ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 4) (pk 1)) (enc (pair (N 6) (N 6)) (r 100) (pk 1)))]) ~ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) /\ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) ~ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))])).
split.
rewrite <- H3.
reflexivity.
reflexivity.
apply if1 with (b := EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) ) (w:= [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (x := (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 4) (pk 1)) (enc (pair (N 6) (N 6)) (r 100) (pk 1))) ) (y := (enc (pair (N 6) (N 6)) (r 5) (pk 1))) (z := (enc (pair (N 6) (N 6)) (r 5) (pk 1))) in H5.
simpl in H5.  
rewrite H5.
(**************  phi 2' 1  *****************)

assert (H6 : (Fresh [7;8] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3))] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6)); msg (enc (pair (N 6) (N 6)) (r 100) (pk 3)) ;msg (pk 3); msg (sk 3)]) = true) /\ (decocclist_mylist [3] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3))] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6));msg (enc (pair (N 6) (N 6)) (r 100) (pk 3))]) = true)).
split.
simpl.
reflexivity.
reflexivity.
apply EncCCA1 in H6. 
assert (H7 : ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (enc (pair (N 6) (N 6)) (r 8) (pk 3))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (enc (pair (N 6) (N 6)) (r 8) (pk 3))]) /\ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (enc (pair (N 6) (N 6)) (r 100) (pk 3))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (enc (pair (N 6) (N 6)) (r 8) (pk 3))])).
split.
reflexivity.
(******  EncKP is used to prove indistingishability for enc terms with different r **********)
apply EncKP with (v:= ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) ; bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )])) (u:=(pair (N 6) (N 6))) (x' := 8)(x := 100).
split.
simpl.
reflexivity.
split.
reflexivity.
reflexivity.
apply if1 with (b:= (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))) (w:= [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )]) (x:= (enc (pair (N 6) (N 6)) (r 8) (pk 3))) (y:= (enc (pair (N 6) (N 6)) (r 100) (pk 3))) (z:= (enc (pair (N 6) (N 6)) (r 8) (pk 3))) in H7. 
rewrite H7 in H6. 
(******** including phi0 term ***********)
assert (H8 : (Fresh [7;8] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3)) ; msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6)); msg (enc (pair (N 6) (N 6)) (r 100) (pk 3)) ;msg (pk 3); msg (sk 3)]) = true) /\ (decocclist_mylist [3] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3)); msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++  [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6));msg (enc (pair (N 6) (N 6)) (r 100) (pk 3))]) = true)).
split.
simpl.
reflexivity.
reflexivity. 
apply EncCCA1 in H8.
assert (H9 : ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 8) (pk 3))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++  ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 8) (pk 3))]) /\ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 100) (pk 3))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 8) (pk 3))])).
split.
reflexivity.
apply EncKP with (v:= ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ])) (u:=(pair (N 6) (N 6))) (x' := 8)(x := 100).
split.
simpl.
reflexivity.
split.
reflexivity.
reflexivity.
apply if1 with (b:= (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))) (w:= ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ])) (x:= (enc (pair (N 6) (N 6)) (r 8) (pk 3))) (y:= (enc (pair (N 6) (N 6)) (r 100) (pk 3))) (z:=(enc (pair (N 6) (N 6)) (r 8) (pk 3))) in H9.
rewrite H9 in H8.
assert (H10 : ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 7) (pk 3)) (enc (pair (N 6) (N 6)) (r 100) (pk 3)))]) ~ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 8) (pk 3))]) /\ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 8) (pk 3))]) ~ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 8) (pk 3))])).
split.
rewrite <- H8.
reflexivity.
reflexivity.
apply if1 with (b := (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )) (w := [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ) (x := (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 7) (pk 3)) (enc (pair (N 6) (N 6)) (r 100) (pk 3))) ) (y := (enc (pair (N 6) (N 6)) (r 8) (pk 3))) (z := (enc (pair (N 6) (N 6)) (r 8) (pk 3))) in H10.
simpl in H10. 
rewrite H10.
(************ applying EncKP to prove Phi 2 1 ~ Phi 2' 1  ****************)
assert (H11 : (Fresh [5;8] ([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) )] ++ [msg (pair (N 6) (N 6)); msg (pk 1); msg (sk 1); msg (pk 3); msg (sk 3)]) = true) /\ (nodeclist_mylist [1;3] ([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) )] ++ [msg (pair (N 6) (N 6))]) = true) /\ (decocclist_mylist [3] ([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) )] ++ [msg (pair (N 6) (N 6))]) = true)).
split.
simpl.
reflexivity.
split.
reflexivity.
reflexivity.
apply EncKP in H11.
apply H11.
Qed.

(*
Theorem verification:([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (if_then_else_M (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1)) (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1); (N 2); (N 3); (pk 1); (pk 2);(pk 3); (enc ( pair (pk 3) (N 6)) (r 4) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 4) (pk 1)) (enc (pair (N 6) (N 6)) (r 5) (pk 1))) (enc (pair (N 6) (N 6)) (r 5) (pk 1))) ]) ~ ([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg ( if_then_else_M (EQ_M (pi1 (dec (f [(N 1);  (N 2); (N 3);(pk 1); (pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 4) (pk 2) ) ]) (sk 2))) (pk 3)) (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1);  (N 2); (N 3); (pk 1); (pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 4) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 5) (pk 3)) (enc (pair (N 6) (N 6)) (r 4) (pk 3))) (enc (pair (N 6) (N 6)) (r 4) (pk 3)) )]) .
Proof.
intros.
simpl.
(*******************  phi 2 1 ************************)
assert (H1 : (Fresh [4;5] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1))] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6)); msg (enc (pair (N 6) (N 6)) (r 5) (pk 1)) ;msg (pk 1); msg (sk 1)]) = false) /\ (decocclist_mylist [1] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1))] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6));msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) = true)).
split.
simpl.
reflexivity.
reflexivity.  
apply EncCCA1 in H1. 
assert (H2 : ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) /\ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))])).
split.
reflexivity.
reflexivity.
apply if1 in H2. 
(* apply if1 with (b:= ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))])) (w:= [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )]) (x:= ([msg (enc ( pair (N 6) (N 6) ) (r 5) (pk 1))]) ) (y:= [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))] ) (z:= ([msg (enc ( pair (N 6) (N 6) ) (r 5) (pk 1))]) ) in H2.
*)
rewrite H2 in H1. 

assert (H3 : (Fresh [4;5] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1)) ; msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6)); msg (enc (pair (N 6) (N 6)) (r 5) (pk 1)) ;msg (pk 1); msg (sk 1)]) = false) /\ (decocclist_mylist [1] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1)); msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++  [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6));msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) = true)).

split.
reflexivity.
reflexivity. 
apply EncCCA1 in H3.
 assert (H4 : ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++  ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) /\ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))])).
split.
reflexivity.
reflexivity.
apply if1 in H4.
rewrite H4 in H3.
assert (H5 : ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 4) (pk 1)) (enc (pair (N 6) (N 6)) (r 5) (pk 1)))]) ~ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) /\ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))]) ~ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 1) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 5) (pk 1))])).
split.
rewrite <- H3.
reflexivity.
reflexivity.
apply if1 in H5.
simpl in H5. 
rewrite H5.

(**************  phi 2' 1  *****************)
assert (H6 : (Fresh [5;4] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3))] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6)); msg (enc (pair (N 6) (N 6)) (r 4) (pk 3)) ;msg (pk 3); msg (sk 3)]) = false) /\ (decocclist_mylist [3] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3))] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6));msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) = true)).
split.
reflexivity.
reflexivity.
apply EncCCA1 in H6.
assert (H7 : ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) /\ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ [bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))])).
split.
reflexivity.
reflexivity.
apply if1 in H7.

rewrite H7 in H6. 

assert (H8 : (Fresh [5;4] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3)) ; msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6)); msg (enc (pair (N 6) (N 6)) (r 4) (pk 3)) ;msg (pk 3); msg (sk 3)]) = false) /\ (decocclist_mylist [3] ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3)); msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++  [msg (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)); msg (pair (N 6) (N 6));msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) = true)).
split.
reflexivity.
reflexivity.
apply EncCCA1 in H8.
 assert (H9 : ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++  ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) /\ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) ~ ([bol (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6)))] ++ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))])).
split.
reflexivity.
reflexivity.
apply if1 in H9.
rewrite H9 in H8.  
assert (H10 : ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (if_then_else_M (EQL (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (pair (N 6) (N 6))) (enc (pair (pi2 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (N 6)) (r 5) (pk 3)) (enc (pair (N 6) (N 6)) (r 4) (pk 3)))]) ~ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) /\ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))]) ~ ([bol (EQ_M (pi1 (dec (f [(N 1);(N 2);(N 3); (pk 1);(pk 2); (pk 3); (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ]) (sk 2))) (pk 3) )] ++ [msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) ) ] ++ [msg (enc (pair (N 6) (N 6)) (r 4) (pk 3))])).
split. 
rewrite <- H8.
reflexivity.
reflexivity.
apply if1 in H10.
simpl in H10.
rewrite H10.
assert (H11 : (Fresh [5;4] ([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) )] ++ [msg (pair (N 6) (N 6)); msg (pk 1); msg (sk 1); msg (pk 3); msg (sk 3)]) = false) /\ (nodeclist_mylist [1;3] ([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) )] ++ [msg (pair (N 6) (N 6))]) = true) /\ (decocclist_mylist [3] ([msg (N 1); msg (N 2); msg (N 3); msg (pk 1); msg (pk 2); msg (pk 3); msg (enc ( pair (pk 3) (N 6)) (r 1) (pk 2) )] ++ [msg (pair (N 6) (N 6))]) = true)).
split. 
reflexivity.
split.
reflexivity. 
reflexivity. 
apply EncKP in H11.
apply H11.
Qed.
*)

