(* term-project_sieve.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2019-2020 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Sat 04 Apr 2020 *)

(* ********** *)

(* name: Chu Jincong	
   email address: chu.jincong@u.yale-nus.edu.sg
   student number: A0156290E

   other members of the group:
   name: Liu Chengpei
   name: Zhi Yi Yeo
   name: Zhang Liu
*)

(* ********** *)
let iota n_init =
 (* iota : int -> int list *)
  assert (n_init >= 0);
  let rec visit n a =
    match n with
    | 0 ->
       a
    | _ ->
       let n' = pred n
       in visit n' (n' :: a)
  in visit n_init [];;

(* ********** *)

type 'a stream =
  | Scons of 'a * 'a stream Lazy.t;;

let shd (Scons (v, _)) =
 (* shd : 'a stream -> 'a *)
  v;;

let stl (Scons (_, ds)) =
 (* stl : 'a stream -> 'a stream *)
  Lazy.force ds;;

let stream_nth s n =
 (* stream_nth : 'a stream -> int -> 'a *)
  assert (n >= 0);
  let rec loop n (Scons (v, s')) =
    if n = 0
    then v
    else loop (pred n) (Lazy.force s')
  in loop n s;;

(* ********** *)

let make_stream seed_init next =
 (* make_stream : 'a -> ('a -> 'a) -> 'a stream *)
  let rec emanate seed_current =
       (* emanate : 'a -> 'a stream *)
    Scons (seed_current, lazy (emanate (next seed_current)))
  in emanate seed_init;;

let prefix_stream s n =
 (* prefix_stream : 'a stream -> int -> 'a list *)
  assert (n >= 0);
  let rec visit n (Scons (v, ds')) =
    if n = 0
    then []
    else let ih = visit (pred n) (Lazy.force ds')
         in v :: ih
  in visit n s;;

let map_stream f s =
 (* map_stream : ('a -> 'b) -> 'a stream -> 'b stream *)
  let rec visit (Scons (v, ds)) =
       (* visit : 'a stream -> 'b stream *)
    Scons (f v, lazy (visit (Lazy.force ds)))
  in visit s;;

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> 
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a);;

let nats = make_stream 0 succ;;

let posnats = make_stream 1 succ;;

let evens = make_stream 0 (fun i -> i + 2);;

let odds = make_stream 1 (fun i -> i + 2);;

(*---Question 1----------*)
let test_strike candidate =
  let b0 = (prefix_stream (candidate nats 0) 20 = prefix_stream evens 20)
  and b1 = (prefix_stream (candidate posnats 0) 20 = prefix_stream odds 20)
  and b2 = (prefix_stream (candidate nats 1) 5 = [0;1;3;4;6])
  and b3 = (prefix_stream (candidate posnats 1) 5 = [1;2;4;5;7])
  and b4 = (prefix_stream (candidate nats 2) 5 = [0;1;2;4;5])
  and b5 = (prefix_stream (candidate posnats 2) 5 = [1;2;3;5;6])
  in b0 && b1 && b2 && b3 && b4 && b5;;

let strike_out s n =
  let () = assert (n >= 0) in
  let m = n+2 in 
  let rec visit i (Scons (v, s')) =
    if i = 1 then visit m (Lazy.force s')
    else Scons(v, lazy(visit (pred i) (Lazy.force s')))
  in visit m s;;

let () = assert (test_strike strike_out);;

(*---Question 2--------*)
let posneg1 = make_stream 1 (fun i -> i* -1);;
let alt10 = make_stream 1 (fun i -> if i=1 then 0 else 1);;
let squares = map_stream (fun i -> i*i) posnats;;
let zeros = make_stream 0 (fun i -> i);;
let onezeros = make_stream 1 (fun i -> 0);;
let ones = make_stream 1 (fun i -> 1);;

let test_scan candidate =
  let b0 = (prefix_stream (candidate posneg1) 20 = prefix_stream alt10 20)
  and b1 = (prefix_stream (candidate onezeros) 20 = prefix_stream ones 20)
  and b2 = (prefix_stream(candidate ones) 20 = prefix_stream posnats 20)
  and b3 = (prefix_stream (candidate odds) 20 = prefix_stream squares 20)
  in b0 && b1 && b2 && b3;;

let scan s =
  let rec visit (Scons (v, s')) a =
    let b = v+a in 
    Scons(b, lazy(visit(Lazy.force s') b))
  in visit s 0;;

let () = assert (test_scan scan);;

(*---Question 3--------*)
let test_composite candidate =
  let b0 = (prefix_stream (candidate posneg1 0) 20 = prefix_stream posnats 20)
  and b1 = (prefix_stream (candidate onezeros 5) 20 = prefix_stream ones 20)
  and b2 = (prefix_stream(candidate ones 3) 20 = prefix_stream posnats 20)
  and b3 = (prefix_stream (candidate odds 0) 5 = [1;6;15;28;45])
  in b0 && b1 && b2 && b3;;

let composite s n =
  let a = strike_out s n
  in scan a;;

let () = assert (test_composite composite);;

(*---Question 4--------*)
let powers m n =
  let rec visit base power = 
    match base with
    | 0 -> []
    | i -> (pow (m+1-i) power):: visit (i-1) power
  in visit m n;;
  
let test_sieve candidate =
  let b0 = (prefix_stream (candidate onezeros 0) 20 =prefix_stream (composite onezeros 0) 20)
  and b1 = (prefix_stream (candidate onezeros 1) 20 =prefix_stream posnats 20)
  and b2 = (prefix_stream (candidate onezeros 2) 20 =prefix_stream squares 20)
  and b3 = (prefix_stream (candidate posneg1 3) 20 =prefix_stream (composite (composite (composite (composite posneg1 3) 2) 1) 0) 20)
  and b4 = (prefix_stream (candidate onezeros 4) 10 = [1; 16; 81; 256; 625; 1296; 2401; 4096; 6561; 10000])
  and b5 = let n = Random.int 100 in (prefix_stream (candidate onezeros n) n = powers n n)  
in b0 && b1 && b2 && b3 && b4 && b5;;

let sieve s k =
  let () = assert (k >= 0) in
  let rec visit s i =
    if i = k
    then composite s i
    else composite (visit s (succ i)) i
  in visit s 0;;

let () = assert (test_sieve sieve);;

(*---Question 5--------*)
(*a*)
(* sieve ones n = sieve onezeros (n+1) *)
let test_sieve_a candidate =
  let b1 = (prefix_stream (candidate ones 0) 20 = prefix_stream posnats 20)
  and b2 = (prefix_stream (candidate ones 1) 20 = prefix_stream squares 20)
  and b3 = (prefix_stream (candidate ones 2) 20 = prefix_stream (sieve onezeros 3) 20)
  and b4 = (prefix_stream (candidate ones 3) 10 = [1; 16; 81; 256; 625; 1296; 2401; 4096; 6561; 10000])
  and b5 = (prefix_stream (candidate posneg1 3) 20 = prefix_stream (composite (composite (composite (composite posneg1 3) 2) 1) 0) 20)
  and b6 = let n = Random.int 100 in (prefix_stream (candidate ones n) 20 = prefix_stream (sieve onezeros (n+1)) 20)
  in b1 && b2 && b3 && b4 && b5 && b6;;

let () = assert (test_sieve_a sieve);;

(*b*)
(* sieve posnats n = sieve onezeros (n+2) *)
let test_sieve_b candidate =
  let b0 = (prefix_stream (candidate posnats 0) 10 = prefix_stream (candidate onezeros 2) 10)
  and b1 = (prefix_stream (candidate posnats 1) 10 = prefix_stream (candidate onezeros 3) 10)
  and b2 = (prefix_stream (candidate posnats 2) 10 = [1; 16; 81; 256; 625; 1296; 2401; 4096; 6561; 10000])
  and b3 = (prefix_stream (candidate posneg1 3) 20 =prefix_stream (composite (composite (composite (composite posneg1 3) 2) 1) 0) 20)
  and b4 = let n = Random.int 100 in (prefix_stream (candidate posnats n) 20 = prefix_stream (sieve onezeros (n+2)) 20)
  in b0 && b1 && b2 && b3 && b4;;

let () = assert (test_sieve_b sieve);;

(*c*)
let test_sieve_c candidate =
  let b0 = (prefix_stream (candidate squares 0) 10 = prefix_stream (candidate(candidate onezeros 2) 0) 10) 
  and b1 = (prefix_stream (candidate squares 1) 10 = prefix_stream (candidate(candidate onezeros 2) 1) 10)
  and b2 = (prefix_stream (candidate squares 2) 10 = prefix_stream (candidate(candidate onezeros 2) 2) 10)
  and b3 = let n = Random.int 100 in (prefix_stream (candidate squares n) 10 =prefix_stream (candidate(candidate onezeros 2) n) 10)
  in b0 && b1 && b2 && b3;;

let () = assert (test_sieve_c sieve);;

(*---Question 6--------*)
(* "sieve tenzeros n" scales each element of "sieve onezeros n" by 10*)
(* "sieve twozeros n" scales each element of "sieve onezeros n" by 2*)
(* "sieve xzeros n" scales each element of "sieve onezeros n" by x*)
let tenzeros = make_stream 10 (fun i-> 0);;
let twozeros = make_stream 2 (fun i -> 0);;
let hundzeros = make_stream 100 (fun i -> 0);;
let tens = make_stream 10 (fun i -> 10);;

let tentimes l =
  List.map (fun i -> 10*i) l;;

let twice l =
  List.map (fun i -> 2*i) l;;

let hundtimes l =
  List.map (fun i -> 100*i) l;;

let test_sieve_6 candidate =
  let b0 = (prefix_stream (candidate tenzeros 0) 10 = tentimes(prefix_stream (candidate onezeros 0) 10))
  and b1 = (prefix_stream (candidate tenzeros 1) 10 = tentimes(prefix_stream (candidate onezeros 1) 10))
  and b2 = (prefix_stream (candidate twozeros 2) 10 = twice(prefix_stream (candidate onezeros 2) 10))
  and b3 = (prefix_stream (candidate hundzeros 3) 10 = hundtimes(prefix_stream (candidate onezeros 3) 10))
  in b0 && b1 && b2 && b3;;

let () = assert (test_sieve_6 sieve);;

(*---Question 7--------*)
let onetwos = make_stream 1 (fun i-> 2);;
let onetens = make_stream 1 (fun i-> 10);;
let onehunds = make_stream 1 (fun i -> 100);;

let test_sieve_7 candidate =
  let b0 = (prefix_stream (candidate onetwos 0) 10 = prefix_stream odds 10)
  and b1 = (prefix_stream (candidate onetwos 1) 10 = List.mapi (fun n a-> (n+1)*a )(prefix_stream odds 10))
  and b2 = (prefix_stream (candidate onetwos 2) 10 = List.mapi (fun n a -> (n+1)*(n+1)*a)(prefix_stream odds 10))
  and b3 = (prefix_stream (candidate onetwos 3) 10 = List.mapi (fun n a -> a* pow(n+1) 3)(prefix_stream odds 10))
  and b4 = (prefix_stream (candidate onetwos 4) 10 = List.mapi (fun n a -> a* pow(n+1) 4)(prefix_stream odds 10))
  and b5 = (prefix_stream (candidate onetens 4) 10 = List.mapi (fun n a -> a* pow(n+1) 4)(prefix_stream (make_stream 1 (fun i -> i+10)) 10))
  and b6 = (prefix_stream (candidate onehunds 4) 10 = List.mapi (fun n a -> a* pow(n+1) 4)(prefix_stream (make_stream 1 (fun i -> i+100)) 10))
  in b0 && b1 && b2 && b3 && b4 && b5 && b6;;

let () = assert (test_sieve_7 sieve);;

(*---Question 8--------*)
let test_sieve_8 candidate =
  let b0 = (prefix_stream (candidate (make_stream 1 (fun i-> 5)) 3) 10 = List.mapi (fun n a -> a* pow (n+1) 3) (prefix_stream (make_stream 1 (fun i -> i+5)) 10))
  and b1 = (prefix_stream (candidate (make_stream 1 (fun i-> 6)) 9) 10 = List.mapi (fun n a -> a* pow (n+1) 9) (prefix_stream (make_stream 1 (fun i -> i+6)) 10))
  and b2 = (prefix_stream (candidate (make_stream 1 (fun i-> 4)) 5) 10 = List.mapi (fun n a -> a* pow (n+1) 5) (prefix_stream (make_stream 1 (fun i -> i+4)) 10))
  in b0 && b1 && b2;;

let () = assert (test_sieve_8 sieve);;


            
