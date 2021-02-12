(*Jincong Chu, Zhi Yi Yeo, Chengpei Liu, Liu Zhang *)
(* Intro to CS Mini-project: Palindromes, string concatenation, and string reversal *)

(* liu-palindromes.ml *)
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

(* ------- Preliminaries ------- *)

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

(*
   # Stringy.init 4 (fun i -> 'a');;
   - : string = "aaaa"
   # Stringy.init 4 (fun i -> char_of_int (i + int_of_char 'a'));;
   - : string = "abcd"
   # 
*)

(* Question 1 *)

(* unit test*)
let test_string_conca t =
  let b0 = (t "" "" = "")
  and b1 = (t "" "a" = "a")
  and b2 = (t "a" "" = "a")
  and b3 = (t "intro" "CS" = "introCS")
  and b4 = (t "Happy" "Recess" ="HappyRecess")
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4;;

let () = assert (test_string_conca (fun s1 s2 -> s1^s2));; 
(* end of unit test*)

let string_conca s1 s2 =
  let len1 = String.length s1
  in let len = len1 + String.length s2
      in let get_character i =
           if i<len1
           then String.get s1 (i)
           else String.get s2 (i-len1)
  in Stringy.init len get_character;;

let () = assert (test_string_conca string_conca);;


let string_conca_bugged s1 s2 =
  if String.length s1 + String.length s2 <= 200
  then string_conca s1 s2
  else "Gotcha!";;

let () = assert (test_string_conca string_conca_bugged);;

(* ********** *)

(* Question 2 *)

let test_string_reverse t =
  let b0 = (t "" = "")
  and b1 = (t "a" = "a")
  and b2 = (t "aba" = "aba")
  and b3 = (t "abba" = "abba")
  and b4 = (t "123456" ="654321")
  and b5 = (t "fakeYale" ="elaYekaf")
  and b6 = (t "ABCDEFGHIJKLMN" = "NMLKJIHGFEDCBA")
  and b7 = (t (t "ASDF") = "ASDF")
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7;;

let string_reverse_mapi s =
  let len = String.length s
  in Stringy.mapi (fun i c -> String.get s (len-i-1)) s;;

let () = assert (test_string_reverse string_reverse_mapi);;

let string_reverse_rec s =
  let len = String.length s
  in let rec visit n =
    if n = 0
    then ""
    else let n' = n - 1
         in let ih = visit n'
            in  ih ^ String.make 1 (String.get s (len-n))
  in visit len;;

let () = assert (test_string_reverse string_reverse_rec);;


let string_reverse_bugged s =
  let len = String.length s
  in if len <= 100
     then string_reverse_mapi s
     else "Gotcha!";;

let () = assert (test_string_reverse string_reverse_bugged);;

(* ********** *)

(* Question 3 *)

let test_string_reverse_for_question_3 t =
  let b0 = (t ""  "")
  and b1 = (t "a"  "asdf")
  and b2 = (t "aba"  "wefs")
  and b3 = (t "abba"  "123")
  and b4 = (t "123456" "654321")
  and b5 = (t "fakeYale" "elaYekaf")
  and b6 = (t "ABCDEFGHIJKLMN"  "OPQRSTUVWXYZ")
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6;; 

(*Our conjecture is that string_reverse (s1^s2) = (string_reverse s2) ^ (string_reverse s1) *)

let test_string_reverse_mapi s1 s2 =
  string_reverse_mapi (s1^s2) = string_reverse_mapi s2 ^ string_reverse_mapi s1;;

let () = assert (test_string_reverse_for_question_3 test_string_reverse_mapi);;

let test_string_reverse_rec s1 s2 =
  string_reverse_rec (s1^s2) = string_reverse_rec s2 ^ string_reverse_rec s1;;

let () = assert (test_string_reverse_for_question_3 test_string_reverse_rec);;

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

(* define a reverse function using a fold function *)

let  string_map_right_left_v3 s=
  (* base cases: *)
  let n = String.length s
  in let () = assert (n >= 0)
     in let (index,str_n) = fold_right_nat (n,"") (fun (ind,str_n') -> (ind-1, str_n' ^ String.make 1 (String.get s (ind-1)))) n
     in str_n;;

let () = assert(test_string_reverse string_map_right_left_v3 );;

(* ********** *)

(* Question 4 *)


(*Append reverse directly*)
let make_palindrome_v1 s =
  s ^ (string_reverse_mapi s);;

(*Append reverse and delete duplicate middle character*)
let make_palindrome_v2 s =
  let len = String.length s
  in let short_string = String.sub s 0 (len-1)
  in  short_string ^ (String.sub s (len-1) 1) ^( string_reverse_mapi short_string);;


(*Repeat string and append reverse directly*)
let make_palindrome_v3 s =
  make_palindrome_v1 (s^s);;

(*Repeat the first character and apply to v2*)
let make_palindrome_v4 s=
  let () = assert (s != "")
    in  make_palindrome_v2 ((String.make 1 (String.get s 0) ) ^ s);;

(*Generate a random lower case character at the end and apply to v1*)
let make_palindrome_v5 s =
  let a = Char.chr (Char.code 'a' + Random.int 26)
    in make_palindrome_v1 (s^ String.make 1 a);;


(*Palindrome generation*)
make_palindrome_v1 "Yale-NUS";;
make_palindrome_v2 "Yale-NUS";;
make_palindrome_v3 "Yale-NUS";;
make_palindrome_v4 "Yale-NUS";;
make_palindrome_v5 "Yale-NUS";;
make_palindrome_v1 "a";;
make_palindrome_v2 "a";;
make_palindrome_v3 "a";;
make_palindrome_v4 "a";;
make_palindrome_v5 "a";;
make_palindrome_v1 "Chengpei";;
make_palindrome_v2 "Chengpei";;
make_palindrome_v3 "Chengpei";;
make_palindrome_v4 "Chengpei";;
make_palindrome_v5 "Chengpei";;
(* ********** *)

(* Question 5 *)

let test_palindromep t =
  let b0 = (t "")
  and b1 = (t "a")
  and b2 = (t "aba" )
  and b3 = (t "abba" )
  and b4 = not (t "123456")
  and b5 = (t "Yale-NUSUN-elaY")
  and b6 = (t "ChengpeiChengpeiiepgnehCiepgnehC")
  and b7 = not (t "abc")
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7;;

let palindromep_mapi s =
  let len = String.length s
  in let reverse = Stringy.mapi (fun i c -> String.get s (len-i-1)) s
  in reverse = s;;

let () = assert (test_palindromep palindromep_mapi);;

let palindromep_rec s =
  let len = String.length s
  in let rec visit n =
    if n <= len /2
    then true 
    else let n' = n - 1
         in let ih = visit n'
            in  ih && (String.get s (n-1) = String.get s (len-n))
     in visit len;;

let () = assert (test_palindromep palindromep_rec);;


let palindromep_bugged s =
  if String.length s <= 100
  then palindromep_mapi s
  else false;;

let () = assert (test_palindromep palindromep_bugged);;

(* ********** *)

(* Question 6 *)

let test_reverse_palindrome t =
  let b0 = (t "" = "")
  and b1 = (t "a" = "a")
  and b2 = (t "aba" = "aba" )
  and b3 = (t "abba" = "abba" )
  and b4 = (t "aaa" = "aaa")
  and b5 = (t "Yale-NUSUN-elaY" = "Yale-NUSUN-elaY")
  and b6 = (t "ChengpeiChengpeiiepgnehCiepgnehC" = "ChengpeiChengpeiiepgnehCiepgnehC")
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6;;


(* Improving the palindromep_rec function: simplifying, reducing number of evaluations *)

let palindromep_rec_v1 s =
  let len = String.length s
  in let rec visit n =
    if n = len /2
    then true 
    else (String.get s (n-1) = String.get s (len-n)) && visit(n - 1)
     in visit len;;

let () = assert (test_palindromep palindromep_rec_v1);;


(* UPDATED with input from Zhi Yi *)
let reverse_palindrome s =
  if palindromep_mapi s
  then s
  else "Ah! You did not input a palindrome";;

let () = assert (test_reverse_palindrome reverse_palindrome);;

let reverse_palindrome_bugged s =
  if String.length s <= 200
  then reverse_palindrome s
  else "Gotcha!";;

let () = assert (test_reverse_palindrome reverse_palindrome_bugged);;

(* ********** *)

(* Question 7 *)

let test_fibonaccize t =
  let b0 = (t "" = " ")
  and b1 = (t "a" = " a")
  and b2 = (t "ab" = " ab" )
  and b3 = (t "abc" = " abcc" )
  and b4 = (t "abcd" = " abccddd")
  and b5 = (t "abcde" = " abccdddeeeee")
  and b6 = (t "abcdef" = " abccdddeeeeeffffffff")
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6;;

let fib_v5 n_given =
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then (0, 1)
    else let n' = n - 1
         in let (fib_n', fib_n) = visit n'
            in (fib_n, fib_n' + fib_n)
  in let (fib_n, fib_succ_n) = visit n_given
     in fib_n;;

let fibonaccize s =
  let len = String.length s
  in let rec visit n =
    if n = len 
    then ""
    else let n' = n + 1
         in let ih = visit n'
            in  String.make (fib_v5 (n+1)) (String.get s n) ^ih
     in " " ^ (visit 0);;

let () = assert (test_fibonaccize fibonaccize);;


let fibonaccize_bugged s =
  if String.length s <= 200
  then fibonaccize s
  else "Gotcha!";;

let () = assert (test_fibonaccize fibonaccize_bugged);;


(*Claim the length of the resulting string equals the fib (String.length s + 2 *)
let test_len_fibonaccize t =
  let b0 = (t "")
  and b1 = (t "a")
  and b2 = (t "ab")
  and b3 = (t "abc")
  and b4 = (t "abcd" )
  and b5 = (t "abcde")
  and b6 = (t "abcdef" )
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6;;

let len_fibonaccize s =
  (String.length (fibonaccize s)) = fib_v5 ((String.length s) + 2);;

let () = assert (test_len_fibonaccize len_fibonaccize);;


(* Another solution that uses the sum function credit to Zhi Yi*)


let sum_v1 f n_given =
  let () = assert(n_given >= 0) in
  let rec visit f n =
    if n = 0
    then f 0
    else let n' = pred n
    	 in let ih = visit f n'
	    in ih + f (succ n')
  in visit f n_given;;


let len_fibonaccize_v2 s =
  (String.length (fibonaccize s)) - 1 = sum_v1 fib_v5 (String.length s);;

let () = assert (test_len_fibonaccize len_fibonaccize_v2);;

(* ********** *)

(* end of liu-palindromes.ml *)
