

Load "IND_MORPHISMS".


(**********************************There exists a natural number which doesn't occur in lists of terms*********************************)
Axiom existsn_mylist: forall (m1 m2 :nat) (nl : ilist nat m1)(bl:mylist m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_mylist n bl = true).
Axiom existsn_Blist : forall (m1 m2 :nat) (nl : ilist nat m1)(bl:ilist Bool m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_blist n bl = true).
Axiom existsn_Mlist: forall (m1 m2 :nat) (nl : ilist nat m1)(ml:ilist message m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_mlist n ml = true).

(***************not(b)*******************************)

Axiom notb: forall (b:Bool)(nt: Bool -> Bool),  (  (nt b) ## ( if_then_else_B b (FAlse) (TRue))).

(*********Axioms for x = y ≡ EQ(x, y) ∼ TRue*****)


Axiom EQindmsg: forall (x y :message),   ( x #  y) <-> [ bol (EQ_M x y)] ~ [ bol TRue] .
Axiom EQindBool: forall ( b1 b2 : Bool), ( b1 ## b2) <-> [bol (EQ_B  b1 b2)] ~ [ bol TRue] .

Axiom EQindmsg1: forall (x y :message),   ( x #  y) -> [ bol (EQ_M x y)] ~ [ bol TRue] .
Axiom EQindBool1: forall ( b1 b2 : Bool), ( b1 ## b2) -> [bol (EQ_B  b1 b2)] ~ [ bol TRue] .

(***********Indistinguishability Axioms*******************************************)
(************************************************************************************)

Check [bol TRue]~[bol FAlse].

Axiom IFDIST: not ([bol TRue]~[bol FAlse]).

Axiom REFL: forall (n:nat)  (ml : mylist n ), ml ~ ml.

Axiom SYM: forall (n:nat) (ml1 : mylist n)( ml2 : mylist n),  ml1~ml2 -> ml2~ml1.

Axiom TRANS: forall (n:nat) (ml1: mylist n)(ml2 : mylist n)( ml3: mylist n),  (ml1~ ml2) /\ (ml2~ ml3) -> ml1~ml3.

Axiom FuncApp_L: forall (m n : nat) (f : mylist n -> mylist m) (ml1 ml2 : mylist n), ml1 ~ ml2 -> (ml1 ++ (f ml1))~ ( ml2 ++ (f ml2)).
Axiom FuncApp_M1: forall (x1 x2 y1 y2: message) (f : message -> message-> Bool), [msg x1; msg x2] ~ [msg y1; msg y2] -> [msg x1; msg x2 ; bol (f x1 x2)] ~ [msg y1; msg y2 ; bol (f y1 y2)].
Axiom FuncApp_B1: forall (b1 b2 b3 b4: Bool) (f : Bool -> Bool -> Bool), [bol b1; bol b2] ~ [bol b3; bol b4] -> [bol b1; bol b2 ; bol (f b1 b2)] ~ [bol b3; bol b4 ; bol (f b3 b4)].

Axiom RESTR : forall ( n m : nat) (ml1 : mylist n) (ml2 : mylist n) (P : mylist n ->  mylist m), ml1 ~ ml2  -> (P ml1) ~ (P ml2) .



(************Axioms for Equality *********)

(***Axiom EQREFL_M : forall (y :message), [EQ_M y y] ~ [TRue].
Axiom EQREFL_B : forall (b:Bool), [EQ_B  b b] ~ [TRue].
Axiom EQCONG_M : forall (x y :message) (f:message -> message), [EQ_M x y ]~[TRue] -> [EQ_M (f x) (f y)]~[TRue].
Axiom EQCONG_B : forall (b1 b2 : Bool) (f: Bool -> Bool), [EQ_B  b1 b2 ]~[TRue] -> [EQ_B  (f b1) (f b2)]~[TRue].***)


(*********Attacker to start new session*******************************)

Axiom Att_new_session: forall x:message,  (EQ_M (act x) new)  ## TRue .

(******Equational theory for DDH**************************************)
(**************************************************************************)
Axiom proj1: forall (m1 m2 :message),  ( <m1 , m2 >1 # m1).
Axiom proj2: forall (m1 m2 : message), ( <m1 , m2 >2 # m2) .
Axiom commexp1: forall (x y g G: message), ( (exp G (exp G g x) y) # (exp G (exp G g y) x)).
Axiom commexp: forall (x y g G: message), ( msg (exp G (exp G g x) y)) ### (msg (exp G (exp G g y) x)).



(*****Axioms for if_then_else *****************)

(**IFSAME**)


Axiom IFSAME_M: forall (b:Bool) (x : message), (if_then_else_M b x x) # x.
Axiom IFSAME_B: forall (b:Bool) (b1 : Bool),  (if_then_else_B b b1 b1) ## b1.


(**IFTRue**)

Axiom IFTRUE_M : forall (x y : message),  (if_then_else_M TRue x y) # x .
Axiom IFTRUE_B : forall (b1 b2 : Bool), (if_then_else_B TRue b1 b2) ## b1.


(**IFFAlse**)

Axiom IFFALSE_M: forall (x y : message), (if_then_else_M FAlse x y) # y.
Axiom IFFALSE_B: forall (b1 b2 : Bool),  (if_then_else_B FAlse b1 b2) ## b2.

(**IFEVAL**)

Axiom IFEVAL_B : forall (b1 b2 : Bool)(n:nat),  (if_then_else_B (Bvar n) b1 b2) ## (if_then_else_B (Bvar n) ([n := TRue] b1) ([n := FAlse] b2)).
Axiom IFEVAL_M : forall (t1 t2 : message) (n:nat),  (if_then_else_M (Bvar n) t1 t2) #(if_then_else_M (Bvar n) ((n := TRue) t1) ((n := FAlse) t2)).
(*
Axiom IFEVAL_B1 : forall (b b1 b2 : Bool)(n:nat) , (if_then_else_B  (Bvar n)  b1   b2) = (if_then_else_B (Bvar n) ([n := TRue] b1) ([n := FAlse] b2)).
Axiom IFEVAL_M1 : forall (t1 t2 : message) (b:Bool) (n:nat),  (if_then_else_M (Bvar n) t1  t2) =  (if_then_else_M (Bvar n) ((n := TRue) t1) ((n := FAlse) t2)).
*)
(*****Equality closed under substitution******)

Axiom Forall_ELM_EVAL_M: forall (x:Bool) (n:nat) (t1 t2 :message), ( t1 # t2 ) ->  ((( n:=x )t1) # ((n:=x)t2)).
Axiom Forall_ELM_EVAL_B: forall (b:Bool) (n:nat) (b1 b2 :Bool), (  b1 ## b2 ) ->  ( ([n:=b] b1) ## ([n:=b] b2)).

Axiom Forall_ELM_EVAL_M1: forall (x:message) (n:nat) (t1 t2 :message), (t1 # t2 ) ->  ({{n:=x}} t1 # {{n:=x}}t2).
Axiom Forall_ELM_EVAL_B1: forall (b:message) (n:nat) (b1 b2 :Bool), ( b1 ## b2 ) ->  ( [[n:=b]] b1 ## [[n:=b]] b2).

Axiom Forall_ELM_EVAL_M2: forall (x:Bool) (n:nat) (t1 t2 :message), (t1 # t2)  ->  ( (( n:=x )t1) # ((n:=x)t2 )).
Axiom Forall_ELM_EVAL_B2: forall (b:Bool) (n:nat) (b1 b2 :Bool), (b1 ## b2)  ->   ( [n:=b] b1 ## [n:=b] b2).

Axiom Forall_ELM_EVAL_M3: forall (x:message) (n:nat) (t1 t2 :message),  ( t1 # t2)  ->  ( {{n:=x}} t1  # {{n:=x}}t2).
Axiom Forall_ELM_EVAL_B3: forall (b:message) (n:nat) (b1 b2 :Bool), ( b1 ## b2) ->   ( [[n:=b]] b1 ## [[n:=b]] b2).

(**************************************************************************IFBRANCH******************************************)
(*********************************************************************************************************************************)

Axiom IFBRANCH_M: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), ([ bol b ; msg x] ++ ml1) ~  ([ bol b'; msg x'] ++ ml2)  ->  ([bol b ; msg y ] ++ ml1) ~([bol b' ; msg y'] ++ ml2)
-> ([bol b ;msg (if_then_else_M b x y)] ++ ml1)~ ([bol b' ; msg (if_then_else_M b x' y')] ++ ml2 ).

Axiom IFBRANCH_B: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(b1 b1' b2 b2':Bool), ([bol b ;bol b1] ++ ml1) ~ ( [bol b' ; bol b1'] ++ ml2)  ->  ([ bol b; bol b2] ++ ml1) ~([bol b'; bol b2'] ++ ml2)
-> ([ bol b ;bol (if_then_else_B b b1 b2)] ++ ml1)~ ( [bol b' ; bol (if_then_else_B b b1' b2')] ++ ml2 ).

(*******************************Axioms for Fresh names*****************************************)

Axiom FRESHNEQ: forall (n : nat) (m : message), ((closed_msg m) = true)/\ ( (Fresh [n] [msg m]) = true) ->[bol (EQ_M (N n) m)]~ [bol FAlse] .

Axiom FRESHIND: forall (n n1 n2:nat) (v w: mylist n), ((closed_mylist (v++w)) = true) /\ ( (Fresh [ n1 ; n2] (v++w)) = true) /\  (v ~ w) <-> ((msg  (N n1) ) +++ v) ~ (( msg (N n2)) +++w ) .
(*************************Auxilary Axioms*********************************)
(****************************************************************************)

Axiom subinlist : forall (m n :nat)(ml : mylist m)(b:Bool) (f: mylist m -> message), (((n:= b)(f ml)) # (f (subbol_mylist n b ml))).
Axiom subinlist1: forall (m n :nat)(ml : mylist m)(b:Bool) (f: mylist m -> Bool), (([n:= b](f ml)) ## (f (subbol_mylist n b ml))).





Axiom subconct: forall (n1 n2 n:nat) (ml1 : mylist n1)(ml2 : mylist n2)(b:Bool), ((subbol_mylist n b (ml1 ++ ml2)) =(subbol_mylist n b ml1 ++ subbol_mylist n b ml2)).
Axiom subinmsg : forall (n : nat)(b:Bool) (t1:message), ( (subbol_os n b (msg t1) ) = (msg ((n := b) t1))).
Axiom subinbol : forall (n : nat)(b:Bool) (t1:Bool), ( (subbol_os n b (bol t1) ) = (bol ([n := b] t1))).

(****************************some axioms***************************)

Axiom notocc_bolmm: forall (n1 n2 : nat) (b: Bool) (m1 m2 : message), (notoccur_msg n1 m2) = true -> ( n1 :=  b)  ((submsg_msg n2 m1)  m2) = (submsg_msg n2 (( n1 := b) m1)) m2 .

(*Axiom occ_bolmm: forall (n1 n2 : nat) (b: Bool) (m1 m2 : message), (notoccur_msg n1 m2) = false -> ( n1 :=  b)  ((submsg_msg n2 m1)  m2) = (submsg_msg n2 (( n1 := b) m1)) (( n1 := b)m2) .*)

Axiom notocc_bolbb : forall  (n1 n2 :nat) (b b1 b2:Bool), (notoccur_bol n1 b2) = true -> ([ n1 :=  b]  [ n2 := b1]  b2)  =    ( [ n2 := ([n1:=b] b1)]  b2) .


(*Axiom occ_bolbb : forall  (n1 n2 :nat) (b b1 b2:Bool), (notoccur_bol n1 b2) = false -> ([ n1 :=  b]  [ n2 := b1]  b2)  =    ( [ n2 := ([n1:=b] b1)]  ([n1:=b] b2)) .*)

Axiom notocc_bolmb : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_bol n1 b1) = true -> ([ n1 :=  b]  [[ n2 := m]]  b1)  =    ( [[ n2 := ((n1 := b) m)]]  b1).

(*Axiom occ_bolmb : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_bol n1 b1) = false -> ([ n1 :=  b]  [[ n2 := m]]  b1)  =    ( [[ n2 := ((n1 := b) m)]]  ([ n1 :=  b] b1)).*)

Axiom notocc_bolbm : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_msg n1 m) = true -> ( ( n1 :=  b)  (( n2 := b1) m)  =    ( ( n2 := ([n1 := b] b1))  m)).

(*Axiom occ_bolbm : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_msg n1 m) = false -> ( ( n1 :=  b)  (( n2 := b1) m)  =    ( ( n2 := ([n1 := b] b1))  (n1 := b)m)).*)



(********************************************************************************)

Axiom notoccn_Bool: forall (n:nat)(b t:Bool), ((notoccur_bol n t) = true )-> ([n := b]t =  t).
Axiom notoccn_msg: forall (n:nat)(b:Bool)(t:message), ((notoccur_msg n t) = true) -> ((n:= b)t) = t.


(***********************************************************************************)
Axiom  invarsub_Bmsg : forall(n:nat)(t:message), ((n:= (Bvar n))t = t).
Axiom invarsub_BBool: forall(n:nat)(b:Bool), ([n:=(Bvar n)] b) = b.
Axiom invarsub_mBool : forall(n:nat)(b: Bool), ([[n:= (Mvar n)]] b) = b. 
Axiom invarsub_mmsg : forall(n:nat)(t: message),{{n:= (Mvar n)}} t = t. 

(*****************************************************************************************************************************************************************)
(****Fresh [n;n1;n2;n3]-> [G(n); g(n);g(n)^(r (n1));g(n)^(r (n2)); g(n)^(r (n1))(r (n2))] ~[G(n); g(n);g(n)^(r (n1));g(n)^(r (n2)); g(n)^(r (n3))]*****************)

Axiom DDH : forall (n n1 n2 n3: nat),  (Fresh [ n ; n1 ;  n2  ; n3 ] []) = true-> 
[ msg (pi1 (ggen (N n))) ; msg (pi2 (ggen (N n))) ; msg (exp (pi1 (ggen (N n))) (pi2 (ggen (N n))) (r ( N n1))) ; msg (exp (pi1 (ggen (N n))) (pi2 (ggen (N n))) (r ( N n2))) ; msg (exp (pi1 (ggen (N n))) (exp (pi1 (ggen (N n))) (pi2 (ggen (N n))) (r (N n1))) (r (N n2)))]
~ [msg (pi1 (ggen (N n))) ; msg (pi2 (ggen (N n))) ; msg (exp (pi1 (ggen (N n))) (pi2 (ggen (N n))) (r (N n1))) ; msg (exp (pi1 (ggen (N n))) (pi2 (ggen (N n))) (r ( N n2))) ; msg (exp (pi1 (ggen (N n))) (pi2 (ggen (N n))) (r (N n3)))]  .

Axiom RESTR_Perm: forall(n1 n2 n3 n4 n5:nat) (nl1 ml1 : mylist n1)(nl2 ml2 : mylist n2)(nl3 ml3 : mylist n3)(ml4 nl4 : mylist n4) (ml5 nl5 : mylist n5), (nl1++nl2++nl3++nl4++nl5)~(ml1++ml2++ml3++ml4++ml5)  -> (nl1 ++nl4++nl2++nl5++nl3)~ (ml1 ++ml4++ml2++ml5++ml3).

(*********************Axiliary axioms****************************)

(***Axiom simpinsub_B : forall (n n1 n2 n3 n4 n5 n6 :nat)(t1 t2 : Bool), (if_then_else_B (Bvar n) [n5 := if_then_else_B TRue (Bvar n1) (Bvar n2)](t1)
   [n6 := if_then_else_B FAlse (Bvar n3) (Bvar n4)](t2))## (if_then_else_B (Bvar n) [n5 := Bvar n1](t1) [n6 := Bvar n4](t2)).**)


