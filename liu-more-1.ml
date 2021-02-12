(*Jincong Chu, Zhi Yi Yeo, Chengpei Liu, Liu Zhang *)
(* Intro to CS Mini-project: More for the road *)

(* liu-more.ml *)
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

(* Question 7 *)


let test_string_map t =
  let b0 = (t (fun c-> 'a') "aasdfasdf" = "aaaaaaaaa")
  and b1 = (t (fun c-> 'b') "aasdfasdf" = "bbbbbbbbb")
  and b2 = (t Char.lowercase_ascii "ABC" = "abc")
  and b3 = (t (fun c->  Char.chr((Char.code c ) +1 )) "abcde" = "bcdef")
  and b4 = (t Char.uppercase_ascii "asdfg" = "ASDFG")
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4;;

let ()=assert(test_string_map String.map);;

let string_map f s =
  let g = fun n c -> f c
    in String.mapi g s;;

let ()=assert(test_string_map string_map);;

(* ********** *)

(* Question 8 *)

let test_string_mapi t =
  let b0 = (t  (fun n c -> Char.chr((Char.code c) +n)) "abcd" = "aceg")
  and b1 = (t (fun n c -> Char.chr((Char.code c) -n)) "aceg" = "abcd")
  and b2 = (t (fun n c -> Char.lowercase_ascii c) "ABC" = "abc")
  and b3 = (t (fun n c -> Char.chr(n + Char.code '0')) "wsfg" = "0123")
  and b4 = (t (fun n c -> Char.uppercase_ascii c) "asdfg" = "ASDFG")
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4;;

let ()=assert (test_string_mapi String.mapi);;

let string_mapi f s =
  let g n = String.map (f n) s
    in let h n = String.get (g n) n 
       in String.init (String.length s) h;;

let ()=assert (test_string_mapi string_mapi);;

(* A more economical solution *)



(* end of liu-more.ml *)
