type 'a list =
| Nil
| Cons of 'a * 'a list

type message =
| Mvar of int
| O
| Acc
| N of int
| If_then_elsem_ of bool * message * message
| Exp of message * message * message
| Pair of message * message
| Pi1 of message
| Pi2 of message
| Ggen of message
| Rr of message
| New
| Act of message
| M of message
| Nonce of message
| Enc of message * message * message
| Dec of message * message
| To of message
| K of message
| Sign of message * message
| Reveal of message
| I of int
| L of message
| Rs of message
| F of message list
and bool =
| Bvar of int
| TRue
| FAlse
| EQB of bool * bool
| EQM of message * message
| If_then_elseb_ of bool * bool * bool
| EQL of message * message
| Ver of message * message * message

(** val size_listrms :
    (int -> message -> int) -> int -> message list -> int **)

let rec size_listrms f n = function
| Nil -> n
| Cons (h, t) -> size_listrms f (f n h) t

(** val size_bol : int -> bool -> int **)

let rec size_bol n = function
| EQB (b1, b2) -> (fun x -> x + 1) (size_bol (size_bol n b1) b2)
| EQM (t1, t2) -> (fun x -> x + 1) (size_msg (size_msg n t1) t2)
| If_then_elseb_ (b1, b2, b3) ->
  (fun x -> x + 1) (size_bol (size_bol (size_bol n b1) b2) b3)
| EQL (t1, t2) -> (fun x -> x + 1) (size_msg (size_msg n t1) t2)
| Ver (t1, t2, t3) ->
  (fun x -> x + 1) (size_msg (size_msg (size_msg n t1) t2) t3)
| _ -> (fun x -> x + 1) n

(** val size_msg : int -> message -> int **)

and size_msg n = function
| Mvar n0 -> (fun x -> x + 1) n0
| If_then_elsem_ (b1, t1, t2) ->
  (fun x -> x + 1) (size_msg (size_msg (size_bol n b1) t1) t2)
| Exp (t1, t2, t3) ->
  (fun x -> x + 1) (size_msg (size_msg (size_msg n t1) t2) t3)
| Pair (t1, t2) -> (fun x -> x + 1) (size_msg (size_msg n t1) t2)
| Pi1 t1 -> (fun x -> x + 1) (size_msg n t1)
| Pi2 t1 -> (fun x -> x + 1) (size_msg n t1)
| Ggen t1 -> (fun x -> x + 1) (size_msg n t1)
| Rr t1 -> (fun x -> x + 1) (size_msg n t1)
| Act t1 -> (fun x -> x + 1) (size_msg n t1)
| M t1 -> (fun x -> x + 1) (size_msg n t1)
| Nonce t1 -> (fun x -> x + 1) (size_msg n t1)
| Enc (t1, t2, t3) ->
  (fun x -> x + 1) (size_msg (size_msg (size_msg n t1) t2) t3)
| Dec (t1, t2) -> (fun x -> x + 1) (size_msg (size_msg n t1) t2)
| To t1 -> (fun x -> x + 1) (size_msg n t1)
| K t1 -> (fun x -> x + 1) (size_msg n t1)
| Sign (t1, t2) -> (fun x -> x + 1) (size_msg (size_msg n t1) t2)
| Reveal t1 -> (fun x -> x + 1) (size_msg n t1)
| L t1 -> (fun x -> x + 1) (size_msg n t1)
| Rs t1 -> (fun x -> x + 1) (size_msg n t1)
| F l -> (fun x -> x + 1) (size_listrms size_msg n l)
| _ -> (fun x -> x + 1) n

