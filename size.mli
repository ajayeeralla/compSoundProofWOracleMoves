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

val size_listrms : (int -> message -> int) -> int -> message list -> int

val size_bol : int -> bool -> int

val size_msg : int -> message -> int

