Load "Pi1_Pi2''".


Axiom IFBRANCH_M1: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), (ml1 ++ [ bol b ; msg x] ) ~  ( ml2 ++ [ bol b'; msg x'])  ->  (ml1 ++ [bol b ; msg y ] ) ~( ml2 ++ [bol b' ; msg y'])
                                                                                          -> (ml1 ++  [ msg (if_then_else_M b x y)])~ ( ml2 ++ [ msg (if_then_else_M b' x' y')]).



Axiom rev_ifbr: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), ([ msg x; bol b] ++ ml1 )  ~   ([ msg x'; bol b'] ++ ml2 ) -> ([ msg y; bol b] ++ ml1 )  ~   ([ msg y'; bol b'] ++ ml2 )
-> ( [msg (if_then_else_M b x y)] ++ ml1 ) ~ (  [ msg (if_then_else_M b' x' y')] ++ ml2).


(****apply IFBRANCH_M repeateadly********************)


Ltac ifbr  ml1 ml2 b b' x x' y y' := pose proof (rev_ifbr _ ml1 ml2 b b' x x' y y');
repeat match goal with
| [H : _ |-  (Cons _ _ (msg (if_then_else_M b x y)) ml1 ) ~  (Cons _ _ (msg (if_then_else_M b' x' y')) ml2 ) ] =>   apply H; clear H; try reflexivity
                           end.
 Ltac ifbr1 :=
repeat match goal with
    | [ |-  (Cons _ _ (msg (if_then_else_M ?B ?X ?Y)) ?L1 )    ~  (Cons _ _ (msg (if_then_else_M ?B' ?X' ?Y')) ?L2 )  ] => ifbr L1 L2 B B' X X' Y Y'
  end.

Ltac ifb := try ifbr1 ; try simpl; try reflexivity; try unf_qb; try unf_qd.


Ltac simpl_Hyps :=
repeat match goal with 
  | [H: _ |- _ ] => simpl in H
    end.

Definition len_mylist {n} (l:mylist n) := n.
Ltac funapp_os p1 t1  := match goal with 
| [H:  ?L1 ~ ?L2 |- _] => apply FUNCApp_os with (p:= p1) (n:= len_mylist L1) (t:= t1) (ml1:= L1) (ml2:= L2) in H; simpl in H
end .

Ltac funos p H1 :=
repeat match goal with  
    | [ |-  (Cons _ _ (msg ?B1 ) _ ) ~ (Cons _ _ (msg ?B2) _) ] => funapp_os p (msg B1) H1
  end.
Ltac DDH2 := assert(DDH1: Fresh [0;1;2;4] [] = true);try reflexivity;
try apply DDH in DDH1.

Axiom RESTR_rev: forall {m} (ml1 ml2: mylist m), ml1 ~ ml2 -> (reverse ml1) ~ (reverse ml2).
(************************************************************************************************)
(************************************************************************************************)
Theorem Pi44_Pi24:  phi44 ~ phi24.

Proof.    

  apply RESTR_rev with (ml1:= (reverse phi44)) (ml2 := (reverse phi24)).

simpl.


 

unfold t45, t25.   
ifb.
ifb.
ifb.
ifb.
ifb.
ifb.
ifb.
ifb.
ifb. 
ifb.

Focus 2.
ifb.
Unfocus.
Focus 3.
ifb.
ifb.
ifb.
ifb.
 
rewrite commexp in DDH1.

apply RESTR_rev in DDH1.  
simpl in DDH1.


restr_swap 1 12  [t14;
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); msg grn21; t13;
    t12; msg (g 0); msg (G 0)]   [t14 ;
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); msg grn4; t13; t12;
   msg (g 0); msg (G 0)].
unfold t14.
repeat ifb.
restr_swap 1 14 [t13 ; bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg grn21; msg O; t12; msg (g 0); msg (G 0)]
   [t13 ; bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; t12; msg (g 0); msg (G 0)].
unfold t13.
repeat ifb.

restr_swap 1 16 [t12; bol (EQ_M (reveal x1) (i 1)); bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg grn21; msg O; msg O; msg (g 0); msg (G 0)]
   [t12; bol (EQ_M (reveal x1) (i 1)); bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12. unf_qa.
repeat ifb.
(*******************)
restr_proj_in 3 DDH1.
 funapp_droplt DDH1.
funapp_droplt DDH1.
funapp_O_in DDH1.
funapp_O_in DDH1.
restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

rev_app funapp_O_in  DDH1; do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.  
(**************************************)


 funapp_droplt DDH1.
funapp_droplt DDH1.
funapp_O_in DDH1.
funapp_O_in DDH1.
restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

rev_app funapp_O_in DDH1.  assumption. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.  
(*************************************************)
restr_swap_in 2 3 DDH1.

 funapp_droplt DDH1.
funapp_O_in DDH1.
funapp_O_in DDH1.
restr_swap_in 3 5 DDH1.
restr_swap_in 4 6 DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
restr_swap_in 1 16 DDH1.
  assumption. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.  auto. 

(***********************************************************)

restr_swap_in 2 3 DDH1.

 funapp_droplt DDH1.
funapp_O_in DDH1.
funapp_O_in DDH1.
restr_swap_in 3 5 DDH1.
restr_swap_in 4 6 DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
restr_swap_in 1 17 DDH1.
  assumption. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto. repeat (try reflexivity).
auto. auto . auto.
aply 3 auto. auto. auto. auto . auto.  auto.

(*******************************************************)


funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
assumption.
 aply 3 auto. auto. auto. auto. auto. auto.
auto. repeat (try reflexivity).
auto. auto . auto.
aply 3 auto. auto. auto. auto . auto.  auto.

(****************************************)
restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
funapp_droplt DDH1.

rev_app funapp_O_in DDH1.
rev_app funapp_O_in  DDH1.
restr_swap_in 1 3 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
rev_app funapp_O_in DDH1.
restr_swap 1 17 [t12 ; bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg grn21; msg O; msg O; msg (g 0); msg (G 0)]
   [t12 ; bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12. unf_qa.
repeat ifb.
assumption.
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
restr_swap_in 1 2 DDH1.
 aply 3 auto. auto. clear DDH1.
(*************************************)
DDH2.
rewrite commexp in DDH1.
apply RESTR_rev in DDH1. simpl in DDH1.

restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_O_in DDH1.
restr_swap_in 1 20 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto.
clear DDH1.
(******************************)


DDH2.
rewrite commexp in DDH1.
apply RESTR_rev in DDH1. simpl in DDH1.

restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))) .
rev_app funapp_O_in DDH1.
restr_swap_in 1 21 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.
clear DDH1.

(****************************************)
DDH2.
rewrite commexp in DDH1.
apply RESTR_rev in DDH1. simpl in DDH1.

funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in  DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))) .
rev_app funapp_O_in DDH1.

assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
(*************************************************************)
unf_qa.
repeat ifb.
restr_swap 1 19 [t12 ; bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg grn21; msg O; msg O; msg (g 0); msg (G 0)]
   [t12 ; bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12. unf_qa. repeat ifb.

funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))) .
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))) .
rev_app funapp_O_in DDH1.
assumption.


 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. 
(******************************************)


funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
rev_app funapp_O_in DDH1.

assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(***********************************************************)


restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_O_in DDH1.
restr_swap_in 1 22 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.

auto.

(******************************************************)





restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
restr_swap_in 1 23 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.

auto. auto.
(*******************************************************)



funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in  DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0 ( bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(****************************************************)


restr_swap 1 20 [t12; bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg grn21; msg O; msg O; msg (g 0); msg (G 0)] 
   [t12 ; bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].

unfold t12. unf_qa.
repeat ifb.

(*************************)



funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

rev_app funapp_O_in DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(*********************************)


funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

rev_app funapp_O_in DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(************************************)



restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).

rev_app funapp_O_in DDH1.
restr_swap_in 1 23 DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.

auto. auto.

(**************************************)


restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
restr_swap_in 1 24 DDH1. 
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.

auto. auto. auto.

(*******************************************************************)



funapp_droplt DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 3 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).

rev_app funapp_O_in DDH1.
assumption. auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(*********************************************************************)
restr_swap 1 21 [t12 ; bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg grn21; msg O; msg acc; msg (g 0); msg (G 0)]
   [t12 ; bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg acc ; msg (g 0); msg (G 0)].
unfold t12 . unf_qa.
repeat ifb.
(***************************************)
rev_app funapp_acc_in DDH1.
aply_in 2 funapp_droplt DDH1.
restr_swap_in 1 2 DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).


rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(****************************************************************)

rev_app funapp_acc_in DDH1.
aply_in 2 funapp_droplt DDH1.
restr_swap_in 1 2 DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).

rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(*********************************************************)



restr_swap_in 2 3 DDH1.
aply_in 1 funapp_droplt DDH1.

rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_acc_in DDH1.
restr_swap_in 1 24 DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(**********************************************************************)


restr_swap_in 2 3 DDH1.
aply_in 1 funapp_droplt DDH1.

rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 ( bol (EQ_M (to x1) (i 2))).
rev_app funapp_acc_in DDH1.
restr_swap_in 1 25 DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(********************************************************************************)

rev_app funapp_acc_in DDH1.
aply_in 2 funapp_droplt DDH1.
restr_swap_in 1 2 DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(*****************************************************************)

restr_swap 1 22 [t12 ; bol (EQ_M (to x2) (i 2)); bol (EQ_M (to x2) (i 1));
    bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg grn21; msg O; msg grn1; msg (g 0); msg (G 0)]
   [t12 ; bol (EQ_M (to x2) (i 2)); bol (EQ_M (to x2) (i 1));
   bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg grn1; msg (g 0); msg (G 0)].
unfold t12; unf_qa.

repeat ifb.

(***********************************************************************)
restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(****************************************************************************)

restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.

funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
rev_app funapp_O_in DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(*************************************************************************)

restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.

funapp_elt_in 1 1 .


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_O_in DDH1.
restr_swap_in 1 24 DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.


(*********************************************)


restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.

funapp_elt_in 1 1 .


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.
restr_swap_in 1 25 DDH1.
assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(******************************************************************)


restr_swap_in 2 3 DDH1.
funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.



funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
 
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in DDH1.

assumption. 
 do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto. auto. auto.  auto. auto. auto. auto. auto.
 auto. do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.

(********************************************************************)

restr_swap 1 22 [t12; bol (EQ_M (to x2) (i 2)); bol (EQ_M (to x2) (i 1));
    bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg grn21; msg O; msg O; msg (g 0); msg (G 0)] [t12 ; bol (EQ_M (to x2) (i 2)); bol (EQ_M (to x2) (i 1));
   bol (EQ_M (reveal x2) (i 2)); bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12; unf_qa.
repeat ifb.

(************************************)
aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
rev_app funapp_O_in  DDH1; do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   

(*********************************************************)

aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
rev_app funapp_O_in  DDH1; do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto.


(****************************************************************)
restr_swap_in 2 3 DDH1.
aply_in 1  funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
rev_app funapp_O_in  DDH1. restr_swap_in 1 25 DDH1. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto.

(***********************************************************************)

restr_swap_in 2 3 DDH1.
aply_in 1  funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in  DDH1. restr_swap_in 1 26 DDH1. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto. auto.


(**************************************************************************)


aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0  (bol (EQ_M (to x2) (i 1))).
funapp_os 0  (bol (EQ_M (to x2) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in  DDH1; do_nat 4 auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto. auto.

unfold qa01. repeat ifb.

restr_swap 1 20  [t12 ; bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (to x1) (i 2));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
    bol (EQ_M (reveal x1) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
    bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
    bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
    bol (EQ_M (reveal x2) (i 1));
    bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
    msg grn21; msg O; msg O; msg (g 0); msg (G 0)]  [t12 ; bol (EQ_M (reveal x2) (i 1)); bol (EQ_M (to x1) (i 2));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1));
   bol (EQ_M (reveal x1) (i 1));
   bol
     (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
          (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
        (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
      (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2); bol (EQ_M (to x3) (i 2));
   bol
     ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
       (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
     (EQ_M (act x1) new); bol (EQ_M (reveal x3) (i 2));
   bol (EQ_M (to x2) (i 1)); bol (EQ_M (reveal x2) (i 2));
   bol (EQ_M (reveal x2) (i 1));
   bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
   bol (EQ_M (reveal x1) (i 2)); bol (EQ_M (reveal x1) (i 1)); 
   msg grn4; msg O; msg O; msg (g 0); msg (G 0)].
unfold t12 ; unf_qa. repeat ifb.

(*******************************************************************)



aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).

rev_app funapp_O_in  DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto.

(***********************************************************)

aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
rev_app funapp_O_in  DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto.

(*******************************************************************************)



restr_swap_in 2 3 DDH1.
aply_in 1  funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).

rev_app funapp_O_in  DDH1. restr_swap_in 1 23  DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto. auto.

(*********************************************************************)



restr_swap_in 2 3 DDH1.
aply_in 1  funapp_droplt DDH1.
rev_app funapp_O_in DDH1.
restr_swap_in 1 2 DDH1.


funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0 (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in  DDH1. restr_swap_in 1 24 DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto. auto. auto.


(************************************)

aply_in 2 funapp_droplt DDH1.
aply_in 2 funapp_O_in DDH1.

restr_swap_in 2 4 DDH1.
restr_swap_in 3 5 DDH1.
funapp_os 0  (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0  (bol (EQ_M (reveal x2) (i 1))).
funapp_os 0  (bol (EQ_M (reveal x2) (i 2))).
funapp_os 0 ( bol (EQ_M (to x2) (i 1))) .
funapp_os 0  (bol (EQ_M (reveal x3) (i 2))) .
funapp_os 0  ( bol
      ((((EQ_M (reveal x3) (i 1)) & (EQ_M (to x2) (i 1))) &
        (EQ_M (to x1) (i 1))) & (notb (EQ_M (act x2) new))) &
      (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x3) (i 2))).
 funapp_os 0 (bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) grn1)) & (EQ_M (m x3) grn2)).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
funapp_os 0 (bol (EQ_M (reveal x2) (i 1))).

funapp_os 0 (bol (EQ_M (reveal x1) (i 1))).
funapp_os 0 (bol (EQ_M (reveal x1) (i 2))).
funapp_os 0  (bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)).
funapp_os 0 (bol (EQ_M (to x1) (i 2))).
rev_app funapp_O_in  DDH1. assumption. auto. aply 3 auto. auto. auto. auto. auto. auto.
auto.  repeat (try reflexivity);
auto. auto ; auto.
aply 1 auto. auto. auto. auto.   auto. auto. auto.   auto. auto. auto.   auto.

Admitted.
