
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val add : int -> int -> int **)

let rec add = (+)

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val eqb : int -> int -> bool **)

  let rec eqb = (=)

  (** val leb : int -> int -> bool **)

  let rec leb = (<=)

  (** val ltb : int -> int -> bool **)

  let ltb = (<)

  (** val pow : int -> int -> int **)

  let rec pow = (fun x y -> int_of_float ((float_of_int x) ** (float_of_int y)))
 end

(** val fold_right :
    __ -> __ -> ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right a b f a0 = function
| [] -> a0
| b0::t -> f b0 (fold_right a b f a0 t)

(** val forallb : __ -> ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb a f = function
| [] -> true
| a0::l0 -> (&&) (f a0) (forallb a f l0)

type run = int * int

(** val rle_encode_aux : int -> int -> int list -> run list **)

let rec rle_encode_aux val0 count = function
| [] -> (count,val0)::[]
| h::t ->
  if Nat.eqb h val0
  then rle_encode_aux val0 (Stdlib.Int.succ count) t
  else (count,val0)::(rle_encode_aux h (Stdlib.Int.succ 0) t)

(** val rle_encode : int list -> run list **)

let rle_encode = function
| [] -> []
| h::t -> rle_encode_aux h (Stdlib.Int.succ 0) t

(** val repeat : int -> int -> int list **)

let rec repeat n val0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> val0::(repeat n' val0))
    n

(** val rle_decode : run list -> int list **)

let rec rle_decode = function
| [] -> []
| r::t ->
  let count,val0 = r in
  let rec app l m =
    match l with
    | [] -> m
    | a::l1 -> a::(app l1 m)
  in app (repeat count val0) (rle_decode t)

(** val count_runs_aux : int -> int list -> int **)

let rec count_runs_aux val0 = function
| [] -> Stdlib.Int.succ 0
| h::t ->
  if Nat.eqb h val0
  then count_runs_aux val0 t
  else Stdlib.Int.succ (count_runs_aux h t)

(** val count_runs : int list -> int **)

let count_runs = function
| [] -> 0
| h::t -> count_runs_aux h t

(** val max_int_runtime : int **)

let max_int_runtime = min Stdlib.max_int 1073741823

(** val rle_encode_validated : int list -> (int * int) list option **)

let rle_encode_validated l =
  if (&&)
       (Nat.leb
         (let rec length = function
          | [] -> 0
          | _::l' -> Stdlib.Int.succ (length l')
          in length l) max_int_runtime)
       (forallb __ (fun x -> Nat.ltb x max_int_runtime) l)
  then Some (rle_encode l)
  else None

(** val compute_decode_size_early : run list -> int **)

let compute_decode_size_early runs =
  fold_right __ __ (fun r acc -> add (let x,_ = r in x) acc) 0 runs

(** val rle_decode_validated : (int * int) list -> int list option **)

let rle_decode_validated runs =
  if (&&)
       (forallb __ (fun r ->
         (&&) (Nat.ltb 0 (let x,_ = r in x))
           ((&&) (Nat.leb (let x,_ = r in x) max_int_runtime)
             (Nat.ltb (let _,y = r in y) max_int_runtime))) runs)
       (Nat.leb (compute_decode_size_early runs) max_int_runtime)
  then Some (rle_decode runs)
  else None

(** val rle_encode_aux_maxrun : int -> int -> int -> int list -> run list **)

let rec rle_encode_aux_maxrun max_run val0 count = function
| [] -> (count,val0)::[]
| h::t ->
  if Nat.eqb h val0
  then if Nat.ltb count max_run
       then rle_encode_aux_maxrun max_run val0 (Stdlib.Int.succ count) t
       else (max_run,val0)::(rle_encode_aux_maxrun max_run h (Stdlib.Int.succ
                              0) t)
  else (count,val0)::(rle_encode_aux_maxrun max_run h (Stdlib.Int.succ 0) t)

(** val rle_encode_maxrun : int -> int list -> run list **)

let rle_encode_maxrun max_run = function
| [] -> []
| h::t -> rle_encode_aux_maxrun max_run h (Stdlib.Int.succ 0) t

(** val byte_limit : int **)

let byte_limit = 255

(** val seven_bit_limit : int **)

let seven_bit_limit = 127

(** val rle_encode_byte : int list -> run list **)

let rle_encode_byte = function
| [] -> []
| h::t -> rle_encode_aux_maxrun byte_limit h (Stdlib.Int.succ 0) t

(** val rle_encode_7bit : int list -> run list **)

let rle_encode_7bit = function
| [] -> []
| h::t -> rle_encode_aux_maxrun seven_bit_limit h (Stdlib.Int.succ 0) t

type rle_stream_state =
| Mk_stream_state of int * int * int

(** val current_val : rle_stream_state -> int **)

let current_val = function
| Mk_stream_state (current_val0, _, _) -> current_val0

(** val current_count : rle_stream_state -> int **)

let current_count = function
| Mk_stream_state (_, current_count0, _) -> current_count0

(** val max_run_length : rle_stream_state -> int **)

let max_run_length = function
| Mk_stream_state (_, _, max_run_length0) -> max_run_length0

(** val init_stream_state : int -> rle_stream_state **)

let init_stream_state max_run =
  Mk_stream_state (0, 0, max_run)

(** val stream_push :
    rle_stream_state -> int -> run option * rle_stream_state **)

let stream_push state val0 =
  if Nat.eqb (current_count state) 0
  then None,(Mk_stream_state (val0, (Stdlib.Int.succ 0),
         (max_run_length state)))
  else if Nat.eqb val0 (current_val state)
       then if Nat.ltb (current_count state) (max_run_length state)
            then None,(Mk_stream_state ((current_val state), (Stdlib.Int.succ
                   (current_count state)), (max_run_length state)))
            else (Some
                   ((max_run_length state),(current_val state))),(Mk_stream_state
                   (val0, (Stdlib.Int.succ 0), (max_run_length state)))
       else (Some
              ((current_count state),(current_val state))),(Mk_stream_state
              (val0, (Stdlib.Int.succ 0), (max_run_length state)))

(** val stream_flush : rle_stream_state -> run option **)

let stream_flush state =
  if Nat.eqb (current_count state) 0
  then None
  else Some ((current_count state),(current_val state))

(** val stream_encode_list :
    rle_stream_state -> int list -> run list * rle_stream_state **)

let rec stream_encode_list state = function
| [] -> [],state
| h::t ->
  let opt_run,new_state = stream_push state h in
  let runs,final_state = stream_encode_list new_state t in
  (match opt_run with
   | Some r -> (r::runs),final_state
   | None -> runs,final_state)

(** val max_int_8 : int **)

let max_int_8 = 255

(** val max_int_16 : int **)

let max_int_16 = 65535

(** val max_int_32 : int **)

let max_int_32 = 4294967295

(** val bounded_rle_encode : int -> int list -> run list option **)

let bounded_rle_encode max_val l =
  if forallb __ (fun x -> Nat.leb x max_val) l
  then Some (rle_encode l)
  else None

(** val rle_encode_u8 : int list -> run list option **)

let rle_encode_u8 =
  bounded_rle_encode max_int_8

(** val rle_encode_u16 : int list -> run list option **)

let rle_encode_u16 =
  bounded_rle_encode max_int_16

(** val rle_encode_u32 : int list -> run list option **)

let rle_encode_u32 =
  bounded_rle_encode max_int_32

(** val bounded_rle_decode : int -> run list -> int list option **)

let bounded_rle_decode max_val runs =
  if forallb __ (fun r -> Nat.leb (let _,y = r in y) max_val) runs
  then Some (rle_decode runs)
  else None

(** val rle_decode_u8 : run list -> int list option **)

let rle_decode_u8 =
  bounded_rle_decode max_int_8

(** val rle_decode_u16 : run list -> int list option **)

let rle_decode_u16 =
  bounded_rle_decode max_int_16

(** val rle_decode_u32 : run list -> int list option **)

let rle_decode_u32 =
  bounded_rle_decode max_int_32
