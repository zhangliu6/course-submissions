(*Jincong Chu, Zhi Yi Yeo, Chengpei Liu, Liu Zhang *)
(* The underlying determinism of OCaml *)

(* liu-ocaml.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2019-2020 *)

(* ********** *)

(* name: Liu Zhang
   email address: zhangliu@u.yale-nus.edu.sg
   student number: A0190879J

   other members of the group:
   name: Jincong Chu
   name: Chengpei Liu
   name: Zhi Yi Yeo
*)

(* Version of 10 Mar 2020 *)

(* ********** *)

let show_bool b =
 (* show_bool : bool -> string *)
  if b
  then "true"
  else "false";;

let show_char c =
 (* show_char : char -> string *)
  "'" ^ (if c = '\\' then "\\\\" else if c = '\'' then "\\\'" else String.make 1 c) ^ "'";;

let show_string s =
 (* show_string : string -> string *)
  "\"" ^ s ^ "\"";;

let show_int n =
 (* show_int : int -> string *)
  if n < 0
  then "(" ^ string_of_int n ^ ")"
  else string_of_int n;;

let show_unit () =
 (* show_unit : unit -> string *)
  "()";;

(* ********** *)
let an_int n =
  let () = Printf.printf "processing %s...\n" (show_int n)
  in n;;

let a_bool b =
  let () = Printf.printf "processing %s...\n" (show_bool b)
  in b;;

let a_char c =
  let () = Printf.printf "processing %s...\n" (show_char c)
  in c;;

let a_string s =
  let () = Printf.printf "processing %s...\n" (show_string s)
  in s;;

let a_unit () =
  let () = Printf.printf "processing the unit value...\n"
  in ();;

let a_function f =
 (* a_function : ('a -> 'b) -> 'a -> 'b *)
  let () = Printf.printf "processing a function...\n"
  and _ = fun x -> f x
  in f;;
 
(* ********** *)

(* Question 1: Determining the evaluating order of an arithmetic expression *)
an_int 1 + an_int 10;;

(*
OCaml output:
processing 10...
processing 1...
- : int = 11

Answer: from right to left.
*)

(* ********** *)

(* Question 2: Determining the evaluating order in a function *)
a_function an_int 5;;

(*
OCaml output:
processing a function...
processing 5...
- : int = 5

Answer: from left to right.
 *)

let simple_function x = 5;;
a_function simple_function (a_char 'c');;

(*
processing a function...
processing 7...
- : int = 7
*)

(* Test for the identity function *)
let identity x = x;;
a_function identity an_int 7;;

(*
OCaml output:
processing a function...
processing 7...
- : int = 7
*)

a_function identity an_int (succ (an_int 6));;

(*
OCaml output:
processing 6...
processing a function...
processing 7...
- : int = 7
*)

(* ********** *)

(*Question 3: Determining the evaluating order in let-expressions *)

(* Declare bindings for global let-expression *)
let n = an_int 1 and m = an_int 2;;

(*
OCaml output:
processing 1...
processing 2...
val n : int = 1
val m : int = 2

Answer: from left to right.
*)

(* Declare bindings for local let-expressions *)
let n = an_int 1 and m = an_int 2 in n + m;; 

(*
OCaml output:
processing 1...
processing 2...
- : int = 3

Answer: from left to right.
*)

(*Question 3: Food for thought*)

(an_int 6, an_int 5);;

(*
OCaml output: 
processing 5...
processing 6...
- : int * int = (6, 5)

Answer: from right to left. 
 *)


(an_int 5, an_int 6);; 

(*
processing 6...
processing 5...
- : int * int = (5, 6)
*)


let x1 = an_int 5 and x2 = an_int 6 in x1 + x2;;

(*
processing 5...
processing 6...
- : int = 11
*)

let (x1, x2) = (an_int 5, an_int 6) in x1 + x2;;

(*
processing 6...
processing 5...
- : int = 11
*)

(* ********** *)

(* Question 4: Determinging the evaluating order of conjunction *)

(* the && conjunction *)

a_bool true && a_bool false;;
(*
processing true...
processing false...
 *)

a_bool true && a_bool true;;
(*
processing true...
processing true...
 *)

a_bool false && a_bool true;;
(* processing false...*)

a_bool false && a_bool false;;
(* processing false...*)

(*Answer: conjunction is evaluated from left to right. And when the first arguemnt is false, the second argument will never be evaluated.*)


(* the || conjunction *)

a_bool true || a_bool true;;

(*
processing true...
- : bool = true
*)

a_bool true || a_bool false;;

(*
processing true...
- : bool = true
*)

a_bool false || a_bool true;;

(*
processing false...
processing true...
- : bool = true
*)

a_bool false || a_bool false;; 

(*
processing false...
processing false...
- : bool = false
*)

(* Answer: same evaluating order; but for the || conjunct, both of the arguemnts will be evaluated regardless of the boolean value of the first argument. *)

(* ********** *)

(* Question 5:  warmup! *)

let test_warmup candidate =
  (candidate 'a' 'b' 'c' = "abc");;


(* We then write another unit test that is more complete *)
let test_warmupv2 candidate =
  let b0 = (candidate 'a' 'b' 'c' = "abc")
  and b1 = (candidate '1' '2' '3' = "123")
  and b2 = (candidate '1' ' ' 'a' = "1 a")
  and b3 = (candidate ' ' ' ' ' ' = "   ")
  and b4 = (candidate '$' '!' '&' = "$!&")
  in b0 && b1 && b2 && b3 && b4;;


let warmup c0 c1 c2 =
  String.make 1 c0 ^ String.make 1 c1 ^ String.make 1 c2;;

let warmup_bugged c0 c1 c2 =
  if int_of_char c0 >= 32 && int_of_char c1 >= 32 && int_of_char c2 >= 32
  then String.make 1 c0 ^ String.make 1 c1 ^ String.make 1 c2
  else "Gotcha!";;

let () = assert (test_warmup warmup);;
let () = assert (test_warmupv2 warmup);;
let () = assert (test_warmup warmup_bugged);;
let () = assert (test_warmup warmup_bugged);;

(* ********** *)

(* Question 6: Implement String.map*)

(* Part A *)
let to_next c0 =
 a_char (char_of_int ( int_of_char(c0) + 1));;

String.map to_next "abcd";;

(*
OCaml output:
processing 'b'...
processing 'c'...
processing 'd'...
processing 'e'...
- : string = "bcde"
*)


(* Part B *)

(* The unit test for String.map implementation *)
let test_string_map candidate =
  let b0 = (candidate (fun _ -> 'a') "abcde" = "aaaaa")
  and b1 = (candidate (fun c0 -> char_of_int (int_of_char c0 + 2)) "abcde" = "cdefg")
  and b2 = (candidate (fun _ ->  ' ') "1234" = "    ")
  and b3 = (let n = Random.int 10 in
            candidate (fun _ -> 'p') (String.make n 'a') = (String.make n 'p'))
  in b0 && b1 && b2 && b3;;  

(* implement a left-to-right version of String.map *)
(* group code: a working recursion*)
let string_map_left_right_v0 f s =
  let () = assert (String.length s >= 0) in
  let rec visit n =
    if n = 0
    then ""
    else let n' = n - 1
         in let ih = visit n'
            in ih ^ String.make 1 (f (String.get s n'))
  in visit (String.length s);;

let () = assert (test_string_map string_map_left_right_v0);;

(* First improvement: reducing the number of computatin of String.length*)
let string_map_left_right_v1 f s =
  let n = String.length s
  in let () = assert (n >= 0) in
     let rec visit n =
       if n = 0
       then ""
       else let n' = n - 1
            in let ih = visit n'
               in ih ^ String.make 1 (f (String.get s n'))
  in visit (n);;

let () = assert (test_string_map string_map_left_right_v1);;

(* Second improvement: substitute the definien visit (n-1) for the variable ih*)
let string_map_left_right_v2 f s =
  let n = String.length s
  in let () = assert (n >= 0) in
     let rec visit n =
       if n = 0
       then ""
       else visit (n - 1) ^ String.make 1 (f (String.get s (n-1)))
     in visit (n);;

let () = assert (test_string_map string_map_left_right_v2);;

(* define map function using fold *)

let fold_right_nat zero_case succ_case n_given =
 (* fold_right_nat : 'a -> ('a -> 'a) -> int -> 'a *)
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then zero_case
    else let n' = n - 1
         in let ih = visit n'
            in succ_case ih    (* <-- succ_case takes one argument *)
  in visit n_given;;

let  string_map_left_right_v3 f s =
  (* base cases: *)
  let n = String.length s
  in let () = assert (n >= 0)
     in let (index,str_n) = fold_right_nat (0,"") (fun (ind,str_n') -> (ind+1, str_n' ^ String.make 1 (f (String.get s (ind))))) n
     in str_n;;

let () = assert (test_string_map string_map_left_right_v3);;

(* Part C: implement a right-to-left version of String.map *)
let string_map_right_left_v2 f s =
  let len = String.length s
  in let () = assert (len >= 0) in
     let rec visit n =
       if n = len
       then ""
       else String.make 1 (f (String.get s n)) ^ visit (n + 1)
     in visit (0);;

let () = assert (test_string_map string_map_right_left_v2);;

let  string_map_right_left_v3 f s =
  (* base cases: *)
  let n = String.length s
  in let () = assert (n >= 0)
     in let (index,str_n) = fold_right_nat (n,"") (fun (ind,str_n') -> (ind-1, String.make 1 (f (String.get s (ind-1))) ^  str_n')) n
     in str_n;;

let () = assert (test_string_map string_map_right_left_v3);;

(* ********** *)

(* Question 7: Implement String.mapi*)

(* Insert Stringy module *)
module Stringy = (* added for versions of OCaml that are anterior to 4.02.0 *)
  struct
    (*
       val mapi : (int -> char -> char) -> string -> string
       String.mapi f s calls f with each character of s and its index (in increasing index order) and stores the results in a new string that is returned.
       Since 4.02.0
       https://caml.inria.fr/pub/docs/manual-ocaml/libref/String.html
    *)
    
    let mapi f s =
      let i = ref ~-1
      in String.map (fun c ->
                      i := succ !i;
                      f !i c)
                    s
    (* ***** *)

    (*
       val init : int -> (int -> char) -> string
       String.init n f returns a string of length n, with character i initialized to the result of f i (called in increasing index order).
       Raise Invalid_argument if n < 0 or n > Sys.max_string_length.
       Since 4.02.0
    *)
    let init n f =
      if 0 <= n && n <= Sys.max_string_length
      then mapi (fun i _ -> f i) (String.create n)
      else raise (Invalid_argument "String.create");;
  end;;

(* Part A - write a quick function to see which order characters are accessed in a given string*)
let blam_traced i _ = a_char (char_of_int (i + int_of_char '0'));;

let blam i _ = char_of_int (i + int_of_char '0');;

Stringy.mapi blam_traced "test";;

(*
OCaml output: 
processing '0'...
processing '1'...
processing '2'...
processing '3'...
- : string = "0123"

Answer: 
 *)

(* The unit test function for String.mapi functions in Part B and Part C *)

let test_string_mapi candidate =
  let b0 = (candidate blam "abcde" = "01234")
  and b1 = (candidate (fun i c0 -> char_of_int (int_of_char c0 + i)) "abcde" = "acegi")
  and b2 = (candidate (fun i _ ->  ' ') "1234" = "    ")
  and b3 = (let n = Random.int 10 in
            candidate (fun i _ -> ('p')) (String.make n 'a') = (String.make n 'p'))
  in b0 && b1 && b2 && b3;; 


(* Part B: Implement left-to-right String.mapi *)

let string_mapi_left_right_v2 f s =
  let n = String.length s
  in let () = assert (n >= 0) in
     let rec visit n =
       if n = 0
       then ""
       else visit (n - 1) ^ String.make 1 (f (n-1) (String.get s (n-1)))
     in visit (n);;

let () = assert (test_string_mapi string_mapi_left_right_v2);;


let  string_mapi_left_right_v3 f s =
  (* base cases: *)
  let n = String.length s
  in let () = assert (n >= 0)
     in let (index,str_n) = fold_right_nat (0,"") (fun (ind,str_n') -> (ind+1, str_n' ^ String.make 1 (f ind (String.get s (ind))))) n
     in str_n;;

let () = assert (test_string_mapi string_mapi_left_right_v3);;

(* Part C: implement a right-to-left version of String.mapi *)
let string_mapi_right_left_v2 f s =
  let len = String.length s
  in let () = assert (len >= 0) in
     let rec visit n =
       if n = len
       then ""
       else String.make 1 (f n (String.get s n)) ^ visit (n + 1)
     in visit (0);;

let () = assert (test_string_mapi string_mapi_right_left_v2);;


let  string_map_right_left_v3 f s =
  (* base cases: *)
  let n = String.length s
  in let () = assert (n >= 0)
     in let (index,str_n) = fold_right_nat (n,"") (fun (ind,str_n') -> ((ind-1), String.make 1 (f (ind-1) (String.get s (ind-1))) ^  str_n')) n
     in str_n;;

let () = assert (test_string_mapi string_map_right_left_v3);;

(* For lucidity's sake *)
let string_mapi_bugged f s =
  if String.length s <= 10
  then string_mapi_left_right_v2 f s
  else "Gotcha!";;

let () = assert (test_string_mapi string_mapi_bugged);;

(* ********** *)

(* Question 8: Considering the validity of simplifying expressions *)

(* Part b *)
an_int 5 * 0;;
0;;

(* Part d *)
an_int 5 * 1;;
an_int 5;;

an_int 5 * an_int 1;;
an_int 5 * 1;;


(* ********** *)

(* Question 9: Considering the equality of impure expressions within expressions *)
(* Part a *)
let x1 = an_int 5 and x2 = an_int 6 in (x1, x2);;
(*
processing 5...
processing 6...
- : int * int = (5, 6)
 *)

let x2 = an_int 6 and x1 = an_int 5 in (x1, x2);;
(*
processing 6...
processing 5...
- : int * int = (5, 6)
 *)

(* Part b *)
let x1 = an_int 5 in let x2 = an_int 6 in (x1, x2);;
(*
processing 5...
processing 6...
- : int * int = (5, 6)
 *)

let x2 = an_int 6 in let x1 = an_int 5 in (x1, x2);;
(*
processing 6...
processing 5...
- : int * int = (5, 6)
 *)


(* end of liu-ocaml.ml *)
