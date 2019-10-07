
Require Import Coq.MSets.MSetList.
Require Import Coq.Lists.ListSet.

Load "IND_AXIOMS".


(************************Set of all states************)
Check (3,4).

Definition Q_states :=  list nat.
Check (cons 1 nil).
Check Q_states.

Definition Qf_states:= list nat.

Print Qf_states.

Check nat.

Check eq_nat_dec.
 Hypothesis Aeq_dec : forall (A:Type) (x y:A), {x = y} + {x <> y}.

Fixpoint set_mem (a:nat) (s:Q_states) : bool :=
    match s with
    | nil => false
    | (cons a1 l) =>
        match (eq_nat_dec a a1) with
        | left _ => true
        | right _ => set_mem a l
        end
    end.

Eval compute in (set_mem 1 (cons 1 nil)).

Eval compute in (length (cons 1 nil)).

Fixpoint subset (l1: list nat) (l2: list nat) : bool :=
match l1 with 
|[] => true
| x :: t => 

(**********************Set of transition rules**********)



(*****************transition type**************)

Inductive transition : Type :=
| tr : nat -> list message -> Bool -> nat -> message -> list message -> transition.

(************************set of transitions*****************************)

Definition Tr  := list transition.

Check Tr.













(**********************************************) 













