
(* term-project_about-indexing-data-structures.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2019-2020 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Sun 19 Apr 2020, now with properly polymorphic unit-test functions *)
(* was: *)
(* Version of Wed 08 Apr 2020, now with error messages in the unit-test functions *)
(* was: *)
(* Version of Sun 05 Apr 2020, with a simpler header *)
(* was: *)
(* Version of Sat 04 Apr 2020 *)

(* ********** *)

(* name: Zhi Yi Yeo
   email address: zhiyi.yeo@u.yale-nus.edu.sg
   student number: A0156253H

   other members of the group: 
   name: Liu Zhang
   name: Chengpei Liu
   name: Jincong Chu
*)

(* ********** *)

exception Not_implemented_yet of string;;

(* ********** *)

let show_int n =
  if n < 0
  then "~" ^ string_of_int n
  else string_of_int n;;

let show_char c =
 (* show_char : char -> string *)
  "'" ^ (if c = '\\' then "\\\\" else if c = '\'' then "\\\'" else String.make 1 c) ^ "'";;

let show_string s =
 (* show_string : string -> string *)
  "\"" ^ s ^ "\"";;

let show_option show_yourself ov =
  match ov with
  | None ->
     "None"
  | Some v ->
     "Some " ^ show_yourself v;;

let show_list show_yourself vs =
  match vs with
  | [] ->
     "[]"
  | v :: vs' ->
     let rec show_list_aux v vs' =
       match vs' with
       | [] ->
          show_yourself v
       | v' :: vs'' ->
          (show_yourself v) ^ "; " ^ (show_list_aux v' vs'')
     in "[" ^ show_list_aux v vs' ^ "]";;

let show_array show_yourself a =
  let length_of_a = Array.length a
  in let rec loop i =
       if i = length_of_a
       then "|]"
       else "; " ^ show_yourself (Array.get a i) ^ loop (succ i)
     in if length_of_a = 0
        then "[||]"
        else "[|" ^ show_yourself (Array.get a 0) ^ loop 1;;

(* ********** *)
(*
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
 *)
(* ********** *)

let fold_right_list nil_case cons_case vs =
 (* fold_right_list : 'a -> ('b -> 'a -> 'a) -> 'b list -> 'a *)
  let rec visit vs =
       (* visit : 'b list -> 'a *)
    match vs with
    | [] ->
       nil_case
    | v :: vs' ->
       cons_case v (visit vs')
  in visit vs;;

let fold_left_list nil_case cons_case vs_init =
 (* fold_left_list : 'a -> ('b -> 'a -> 'a) -> 'b list -> 'a *)
  let rec loop vs a =
       (* loop : 'b list -> 'a *)
    match vs with
    | [] ->
       a
    | v :: vs' ->
       loop vs' (cons_case v a)
  in loop vs_init nil_case;;

let fold_right_nat zero_case succ_case n =
 (* fold_right_nat : 'a -> ('a -> 'a) -> int -> 'a *)
  let () = assert (n >= 0) in
  let rec visit i =
    if i = 0
    then zero_case
    else succ_case (visit (pred i))
  in visit n;;

let fold_left_nat zero_case succ_case n =
 (* fold_right_nat : 'a -> ('a -> 'a) -> int -> 'a *)
  let () = assert (n >= 0) in
  let rec loop i a =
    if i = 0
    then a
    else loop (pred i) (succ_case a)
  in loop n zero_case;;

(* ********** *)

type 'a llist =
  | Lnil
  | Lcons of 'a * 'a llist Lazy.t;;

let show_llist show_yourself lvs =
  let rec show_llist_aux lvs =
    match lvs with
    | Lnil ->
       "Lnil"
    | Lcons (v, sc) ->
       "(Lcons (" ^ show_yourself v ^ ", lazy " ^ show_llist_aux (Lazy.force sc) ^ "))"
  in match lvs with
     | Lnil ->
        "Lnil"
     | Lcons (v, sc) ->
        "Lcons (" ^ show_yourself v ^ ", lazy " ^ show_llist_aux (Lazy.force sc) ^ ")";;

let fold_right_llist lnil_case lcons_case lvs_init =
 (* fold_right_llist : 'a -> ('b -> 'a -> 'a) -> 'b llist -> 'a *)
  let rec visit lvs =
       (* visit : 'b llist -> 'a *)
    match lvs with
    | Lnil ->
       lnil_case
    | Lcons (v, dlvs') ->
       let ih = visit (Lazy.force dlvs')
       in lcons_case v ih
  in visit lvs_init;;

let fold_left_llist lnil_case lcons_case lvs_init =
 (* fold_left_llist : 'a -> ('b -> 'a -> 'a) -> 'b llist -> 'a *)
  let rec loop lvs a =
    (* loop : 'b llist -> 'a *)
    match lvs with
    | Lnil ->
       a
    | Lcons (v, dlvs') ->
       loop (Lazy.force dlvs') (lcons_case v a)
  in loop lvs_init lnil_case;;

(* ********** *)

type 'a stream =
  | Scons of 'a * 'a stream Lazy.t;;

(* ********** *)

type 'a binary_tree =
  | Leaf of 'a
  | Node of 'a binary_tree * 'a binary_tree;;

let show_binary_tree show_yourself t =
  (* show_binary_tree : ('a -> string) -> 'a binary_tree -> string *)
  let rec visit t =
    match t with
    | Leaf v ->
       "Leaf " ^ (show_yourself v)
    | Node (t1, t2) ->
       "Node (" ^ visit t1 ^ ", " ^ visit t2 ^ ")"
  in visit t;;

let fold_binary_tree leaf_case node_case t_init =
 (* fold_binary_tree : ('a -> 'b) -> ('b -> 'b -> 'b) -> 'a binary_tree -> 'b *)
  let rec visit t =
    match t with
    | Leaf v ->
       leaf_case v
    | Node (t1, t2) ->
       node_case (visit t1) (visit t2)
  in visit t_init;;

type 'a intermediate_result =
  | Found of 'a
  | Still_looking of int

(* ********** *)

let test_index_string_left_to_right_one name candidate test expected_result given_string given_index =
  let actual_result = candidate given_string given_index
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_index_string_left_to_right failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_option show_char actual_result)
                     (show_option show_char expected_result)
          in false;;

let test_index_string_left_to_right name candidate =
  let b0 = test_index_string_left_to_right_one
             name
             candidate
             "b0"
             (Some '0')
             "0123"
             0
  and b1 = test_index_string_left_to_right_one
             name
             candidate
             "b1"
             (Some '1')
             "0123"
             1
  and b2 = test_index_string_left_to_right_one
             name
             candidate
             "b2"
             (Some '2')
             "0123"
             2
  and b3 = test_index_string_left_to_right_one
             name
             candidate
             "b3"
             (Some '3')
             "0123"
             3
  and b4 = test_index_string_left_to_right_one
             name
             candidate
             "b4"
             None
             "0123"
             4
  and b5 = test_index_string_left_to_right_one
             name
             candidate
             "b4"
             None
             "0123"
             ~-1
  in b0 && b1 && b2 && b3 && b4 && b5;;

(* was:
let test_index_string_left_to_right name candidate =
  let b0 = (candidate "0123" 0 = Some '0')
  and b1 = (candidate "0123" 1 = Some '1')
  and b2 = (candidate "0123" 2 = Some '2')
  and b3 = (candidate "0123" 3 = Some '3')
  and b4 = (candidate "0123" 4 = None)
  and b5 = (candidate "0123" ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;
*)

let index_string_left_to_right_v0 s_given n_given =
  if 0 <= n_given && n_given < (String.length s_given)
  then Some (String.get s_given n_given)
  else None;;

let () = assert (test_index_string_left_to_right "index_string_left_to_right_v0" index_string_left_to_right_v0);;

let index_string_left_to_right_v1 s_given n_given =
  try Some (String.get s_given n_given) with
  | Invalid_argument "index out of bounds" -> None;;

let () = assert (test_index_string_left_to_right "index_string_left_to_right_v1" index_string_left_to_right_v1);;
                         

(* ********** *)

let test_index_string_right_to_left_one name candidate test expected_result given_string given_index =
  let actual_result = candidate given_string given_index
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_index_string_right_to_left failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_option show_char actual_result)
                     (show_option show_char expected_result)
          in false;;

let test_index_string_right_to_left name candidate =
  let b0 = test_index_string_right_to_left_one
             name
             candidate
             "b0"
             (Some '0')
             "3210"
             0
  and b1 = test_index_string_right_to_left_one
             name
             candidate
             "b1"
             (Some '1')
             "3210"
             1
  and b2 = test_index_string_right_to_left_one
             name
             candidate
             "b2"
             (Some '2')
             "3210"
             2
  and b3 = test_index_string_right_to_left_one
             name
             candidate
             "b3"
             (Some '3')
             "3210"
             3
  and b4 = test_index_string_right_to_left_one
             name
             candidate
             "b4"
             None
             "3210"
             4
  and b5 = test_index_string_right_to_left_one
             name
             candidate
             "b4"
             None
             "3210"
             ~-1
  in b0 && b1 && b2 && b3 && b4 && b5;;

(* was:
let test_index_string_right_to_left name candidate =
  let b0 = (candidate "3210" 0 = Some '0')
  and b1 = (candidate "3210" 1 = Some '1')
  and b2 = (candidate "3210" 2 = Some '2')
  and b3 = (candidate "3210" 3 = Some '3')
  and b4 = (candidate "3210" 4 = None)
  and b5 = (candidate "3210" ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;
*)

let index_string_right_to_left_v0 s_given n_given =
  let len = String.length s_given
  in if 0 <= n_given && n_given < len
     then Some (String.get s_given (len - 1 - n_given))
     else None;;

let () = assert (test_index_string_right_to_left "index_string_right_to_left_v0" index_string_right_to_left_v0);;

let index_string_right_to_left_v1 s_given n_given =
  try Some (String.get s_given (String.length s_given - 1 - n_given)) with
  | Invalid_argument "index out of bounds" -> None;;

let () = assert (test_index_string_right_to_left "index_string_right_to_left_v1" index_string_right_to_left_v1);;

(* ********** *)

let test_index_array_left_to_right_one name candidate test show_yourself expected_result given_array given_index =
  let actual_result = candidate given_array given_index
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_index_array_left_to_right failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_option show_yourself actual_result)
                     (show_option show_yourself expected_result)
          in false;;

let test_index_array_left_to_right_int name candidate =
  let b0 = test_index_array_left_to_right_one
             name
             candidate
             "b0"
             show_int
             (Some 0)
             [|0; 1; 2; 3|]
             0
  and b1 = test_index_array_left_to_right_one
             name
             candidate
             "b1"
             show_int
             (Some 1)
             [|0; 1; 2; 3|]
             1
  and b2 = test_index_array_left_to_right_one
             name
             candidate
             "b2"
             show_int
             (Some 2)
             [|0; 1; 2; 3|]
             2
  and b3 = test_index_array_left_to_right_one
             name
             candidate
             "b3"
             show_int
             (Some 3)
             [|0; 1; 2; 3|]
             3
  and b4 = test_index_array_left_to_right_one
             name
             candidate
             "b4"
             show_int
             None
             [|0; 1; 2; 3|]
             4
  and b5 = test_index_array_left_to_right_one
             name
             candidate
             "b4"
             show_int
             None
             [|0; 1; 2; 3|]
             ~-1
  in b0 && b1 && b2 && b3 && b4 && b5;;

(* was:
let test_index_array_left_to_right_int name candidate =
  let b0 = (candidate [|0; 1; 2; 3|] 0 = Some 0)
  and b1 = (candidate [|0; 1; 2; 3|] 1 = Some 1)
  and b2 = (candidate [|0; 1; 2; 3|] 2 = Some 2)
  and b3 = (candidate [|0; 1; 2; 3|] 3 = Some 3)
  and b4 = (candidate [|0; 1; 2; 3|] 4 = None)
  and b5 = (candidate [|0; 1; 2; 3|] ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;
*)

let index_array_left_to_right_v0 a_given n_given =
  if 0 <=  n_given && n_given < (Array.length a_given)
  then Some (Array.get a_given n_given)
  else None;;

let () = assert (test_index_array_left_to_right_int "index_array_left_to_right_v0" index_array_left_to_right_v0);;


let index_array_left_to_right_v1 a_given n_given =
  try Some (Array.get a_given n_given) with
  | Invalid_argument "index out of bounds" -> None;;


let () = assert (test_index_array_left_to_right_int "index_array_left_to_right_v1" index_array_left_to_right_v1);;

(* ********** *)

let test_index_array_right_to_left_one name candidate test show_yourself expected_result given_array given_index =
  let actual_result = candidate given_array given_index
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_index_array_right_to_left failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_option show_yourself actual_result)
                     (show_option show_yourself expected_result)
          in false;;

let test_index_array_right_to_left_int name candidate =
  let b0 = test_index_array_right_to_left_one
             name
             candidate
             "b0"
             show_int
             (Some 0)
             [|3; 2; 1; 0|]
             0
  and b1 = test_index_array_right_to_left_one
             name
             candidate
             "b1"
             show_int
             (Some 1)
             [|3; 2; 1; 0|]
             1
  and b2 = test_index_array_right_to_left_one
             name
             candidate
             "b2"
             show_int
             (Some 2)
             [|3; 2; 1; 0|]
             2
  and b3 = test_index_array_right_to_left_one
             name
             candidate
             "b3"
             show_int
             (Some 3)
             [|3; 2; 1; 0|]
             3
  and b4 = test_index_array_right_to_left_one
             name
             candidate
             "b4"
             show_int
             None
             [|3; 2; 1; 0|]
             4
  and b5 = test_index_array_right_to_left_one
             name
             candidate
             "b4"
             show_int
             None
             [|3; 2; 1; 0|]
             ~-1
  in b0 && b1 && b2 && b3 && b4 && b5;;

(* was:
let test_index_array_right_to_left_int name candidate =
  let b0 = (candidate [|3; 2; 1; 0|] 0 = Some 0)
  and b1 = (candidate [|3; 2; 1; 0|] 1 = Some 1)
  and b2 = (candidate [|3; 2; 1; 0|] 2 = Some 2)
  and b3 = (candidate [|3; 2; 1; 0|] 3 = Some 3)
  and b4 = (candidate [|3; 2; 1; 0|] 4 = None)
  and b5 = (candidate [|3; 2; 1; 0|] ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;
*)

let index_array_right_to_left_v0 a_given n_given =
  if 0 <= n_given && n_given < (Array.length a_given)
  then Some (Array.get a_given (Array.length a_given - 1 - n_given))
  else None;;
             
let () = assert (test_index_array_right_to_left_int "index_array_right_to_left_v0" index_array_right_to_left_v0);;


let index_array_right_to_left_v1 a_given n_given =
  try Some (Array.get a_given (Array.length a_given - 1 - n_given)) with
  | Invalid_argument "index out of bounds" -> None;;

let () = assert (test_index_array_right_to_left_int "index_array_right_to_left_v1" index_array_right_to_left_v1);;

(* ********** *)

let test_index_list_left_to_right_one name candidate test show_yourself expected_result given_list given_index =
  let actual_result = candidate given_list given_index
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_index_list_left_to_right failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_option show_yourself actual_result)
                     (show_option show_yourself expected_result)
          in false;;

let test_index_list_left_to_right_int name candidate =
  let b0 = test_index_list_left_to_right_one
             name
             candidate
             "b0"
             show_int
             (Some 0)
             [0; 1; 2; 3]
             0
  and b1 = test_index_list_left_to_right_one
             name
             candidate
             "b1"
             show_int
             (Some 1)
             [0; 1; 2; 3]
             1
  and b2 = test_index_list_left_to_right_one
             name
             candidate
             "b2"
             show_int
             (Some 2)
             [0; 1; 2; 3]
             2
  and b3 = test_index_list_left_to_right_one
             name
             candidate
             "b3"
             show_int
             (Some 3)
             [0; 1; 2; 3]
             3
  and b4 = test_index_list_left_to_right_one
             name
             candidate
             "b4"
             show_int
             None
             [0; 1; 2; 3]
             4
  and b5 = test_index_list_left_to_right_one
             name
             candidate
             "b4"
             show_int
             None
             [0; 1; 2; 3]
             ~-1
  in b0 && b1 && b2 && b3 && b4 && b5;;

(* was:
let test_index_list_left_to_right_int name candidate =
  let b0 = (candidate [0; 1; 2; 3] 0 = Some 0)
  and b1 = (candidate [0; 1; 2; 3] 1 = Some 1)
  and b2 = (candidate [0; 1; 2; 3] 2 = Some 2)
  and b3 = (candidate [0; 1; 2; 3] 3 = Some 3)
  and b4 = (candidate [0; 1; 2; 3] 4 = None)
  and b5 = (candidate [0; 1; 2; 3] ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;
*)

(* Part a *)
let index_list_left_to_right_v0 vs_given n_given =
  if n_given <0 || n_given > List.length vs_given - 1
  then None
  else Some (List.nth vs_given n_given);;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v0" index_list_left_to_right_v0);;

(* Part b *)
let index_list_left_to_right_v1 vs_given n_given =
  try Some (List.nth vs_given n_given) with
  | Invalid_argument "List.nth" -> None
  | Failure "nth" -> None;;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v1" index_list_left_to_right_v1);;

(* Part c *)
let index_list_left_to_right_v2 vs_given n_given =
  let rec visit vs =
    match vs with
    | [] ->
       None
    | v::vs' ->
       if List.length vs_given - List.length vs = n_given
       then Some v
       else visit vs'
  in visit vs_given;;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v2" index_list_left_to_right_v2);;

let index_list_left_to_right_v3 vs_given n_given =
  let rec visit vs a =
    match vs with
    | [] ->
       None
    | v::vs' ->
       (match a with
        | 0 ->
           Some v
        | _ ->
           visit vs' (pred a))
  in visit vs_given n_given;;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v3" index_list_left_to_right_v3);;

let index_list_left_to_right_v4 vs_given n_given =
  let rec visit vs =
    match vs with
    | [] ->
       (List.length vs_given, None)
    | v :: vs' ->
       let (i, x) = (visit vs')
       in if i = n_given + 1
          then (i-1, Some v)
          else (i-1, x)
  in let (_, x) = visit vs_given
     in x;;
                           
  
let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v4" index_list_left_to_right_v4);; 

let index_list_left_to_right_v5 vs_given n_given =
  let rec visit vs =
    match vs with
    | [] ->
       fun a -> None
    | v :: vs' ->
       fun a -> match a with
                | 0 ->
                   Some v
                | _ ->
                   visit vs' (pred a) 
  in visit vs_given n_given;;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v5" index_list_left_to_right_v5);;

(* Part d *)

let index_list_left_to_right_v6 vs_given n_given =
  (fun (_, x) -> x) (fold_right_list (List.length vs_given, None) (fun v vs' -> let (i, x) = vs'
                                                                                in if i = n_given + 1
                                                                                   then (i-1, Some v)
                                                                                   else (i-1, x)) vs_given);;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v6" index_list_left_to_right_v6);;

let index_list_left_to_right_v7 vs_given n_given =
  fold_right_list (fun a -> None) (fun v vs' a-> if a = 0
                                                 then Some v
                                                 else vs' (pred a))
                                                        vs_given n_given;;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v7" index_list_left_to_right_v7);;



(* Part e *)
let index_list_left_to_right_v8 vs_given n_given =
  if n_given < List.length vs_given && n_given >= 0
  then let rec visit n vs =
         if n = 0
         then Some (List.hd vs)
         else visit (pred n) (List.tl vs)
       in visit n_given vs_given
  else None;;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v8" index_list_left_to_right_v8);;

let index_list_left_to_right_v9 vs_given n_given =
  let rec visit n vs =
    match n with
    | 0 ->
       (match vs with
       | [] ->
          None
       | _ ->
          Some (List.hd vs))
    | _ ->
       (match vs with
       | [] ->
          None
       | _ ->
          visit (pred n) (List.tl vs))
  in visit n_given vs_given;;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v9" index_list_left_to_right_v9);;

let index_list_left_to_right_v10 vs_given n_given =
  let rec visit n =
    fun vs -> match n with
              | 0 ->
                 (match vs with
                  | [] ->
                     None
                  | _ ->
                     Some (List.hd vs))
              | _ ->
                 (match vs with
                  | [] ->
                     None
                  | _ ->
                     visit (pred n) (List.tl vs))
  in visit n_given vs_given;;

let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v10" index_list_left_to_right_v10);;


(* Part f *)
let index_list_left_to_right_v11 vs_given n_given =
  if n_given < 0
  then None
  else  fold_right_nat (fun vs -> if vs = []
                                  then None
                                  else Some (List.hd vs))
          (fun i vs -> if vs = []
                       then None
                       else i (List.tl vs))
          n_given vs_given;;


let () = assert (test_index_list_left_to_right_int "index_list_left_to_right_v11" index_list_left_to_right_v11);;

(* ********** *)

let test_index_list_right_to_left_one name candidate test show_yourself expected_result given_list given_index =
  let actual_result = candidate given_list given_index
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_index_list_right_to_left failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_option show_yourself actual_result)
                     (show_option show_yourself expected_result)
          in false;;

let test_index_list_right_to_left_int name candidate =
  let b0 = test_index_list_right_to_left_one
             name
             candidate
             "b0"
             show_int
             (Some 0)
             [3; 2; 1; 0]
             0
  and b1 = test_index_list_right_to_left_one
             name
             candidate
             "b1"
             show_int
             (Some 1)
             [3; 2; 1; 0]
             1
  and b2 = test_index_list_right_to_left_one
             name
             candidate
             "b2"
             show_int
             (Some 2)
             [3; 2; 1; 0]
             2
  and b3 = test_index_list_right_to_left_one
             name
             candidate
             "b3"
             show_int
             (Some 3)
             [3; 2; 1; 0]
             3
  and b4 = test_index_list_right_to_left_one
             name
             candidate
             "b4"
             show_int
             None
             [3; 2; 1; 0]
             4
  and b5 = test_index_list_right_to_left_one
             name
             candidate
             "b4"
             show_int
             None
             [3; 2; 1; 0]
             ~-1
  in b0 && b1 && b2 && b3 && b4 && b5;;

(* was:
let test_index_list_right_to_left_int name candidate =
  let b0 = (candidate [3; 2; 1; 0] 0 = Some 0)
  and b1 = (candidate [3; 2; 1; 0] 1 = Some 1)
  and b2 = (candidate [3; 2; 1; 0] 2 = Some 2)
  and b3 = (candidate [3; 2; 1; 0] 3 = Some 3)
  and b4 = (candidate [3; 2; 1; 0] 4 = None)
  and b5 = (candidate [3; 2; 1; 0] ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;
*)
(* Part a *)
let index_list_right_to_left_v0 vs_given n_given =
  let len = List.length vs_given in
  if 0 <=  n_given && n_given < len
  then Some (List.nth vs_given (len - n_given - 1))
  else None;;

let () = assert (test_index_list_right_to_left_int "index_list_right_to_left_v0" index_list_right_to_left_v0);;

(* Part b *)
let index_list_right_to_left_v1 vs_given n_given =
  index_list_left_to_right_v0 (List.rev vs_given) n_given;;

let () = assert (test_index_list_right_to_left_int "index_list_right_to_left_v1" index_list_right_to_left_v1);;


(* Part c *)
let index_list_right_to_left_v2 vs_given n_given =
  let rec visit vs =
    match vs with
    | [] ->
       None
    | v::vs' ->
       if List.length vs' = n_given
       then Some v
       else visit vs'
  in visit vs_given;;


let () = assert (test_index_list_right_to_left_int "index_list_right_to_left_v2" index_list_right_to_left_v2);;

let index_list_right_to_left_v3 vs_given n_given =
  let rec visit vs =
    match vs with
    | [] ->
       (n_given, None)
    | v :: vs' ->
       let (i, x) = visit vs'
       in if i = 0
          then (i-1, Some v)
          else (i-1, x)
  in let (_, x) = (visit vs_given)
     in x;;

let () = assert (test_index_list_right_to_left_int "index_list_right_to_left_v3" index_list_right_to_left_v3);;

let index_list_right_to_left_v3' vs_given n_given =
  let rec visit vs =
    match vs with
    | [] ->
       Still_looking n_given
    | v :: vs' ->
       match visit vs' with
       | Still_looking 0 ->
          Found v
       | Still_looking i ->
          Still_looking (i-1)
       | Found v ->
          Found v
  in match (visit vs_given) with
     | Found v ->
        Some v
     | _ ->
        None;;

let () = assert (test_index_list_right_to_left_int "index_list_right_to_left_v3'" index_list_right_to_left_v3');;
 
(* Part d *)
let index_list_right_to_left_v4 vs_given n_given =
  let (_, x) =(fold_right_list (n_given, None) (fun v vs' -> let (i, x) = vs'
                                                             in if i = 0
                                                                then (i-1, Some v)
                                                                else (i-1, x)) vs_given)
  in x;;

let () = assert (test_index_list_right_to_left_int "index_list_right_to_left_v4" index_list_right_to_left_v4);;

(* Subsidiary question *)
(* Part 1 *)
let index_subsidiary_left_to_right vs_given n_given =
  let (_, x) = (fold_left_list (List.length vs_given, None) (fun v vs' -> let (i, x) = vs'
                                                                          in if i = n_given + 1
                                                                             then (i-1, Some v)
                                                                             else (i-1, x)) vs_given)
  in x;;


let () = assert (test_index_list_right_to_left_int "index_subsidiary_left_to_right" index_subsidiary_left_to_right);;

(* Part 2 *)

let index_subsidiary_right_to_left vs_given n_given =
  let (_, x) = (fold_left_list (0, None) (fun v vs' -> let (i, x) = vs'
                                                       in if i = n_given
                                                          then (i+1, Some v)
                                                          else (i+1, x)) vs_given)
  in x;;

let () = assert (test_index_list_left_to_right_int "index_subsidiary_right_to_left" index_subsidiary_right_to_left);;

(* ********** *)

let test_index_llist_left_to_right_one name candidate test show_yourself expected_result given_llist given_index =
  let actual_result = candidate given_llist given_index
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_index_llist_left_to_right failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_option show_yourself actual_result)
                     (show_option show_yourself expected_result)
          in false;;

let test_index_llist_left_to_right_int name candidate =
  let b0 = test_index_llist_left_to_right_one
             name
             candidate
             "b0"
             show_int
             (Some 0)
             (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil))))))))
             0
  and b1 = test_index_llist_left_to_right_one
             name
             candidate
             "b1"
             show_int
             (Some 1)
             (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil))))))))
             1
  and b2 = test_index_llist_left_to_right_one
             name
             candidate
             "b2"
             show_int
             (Some 2)
             (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil))))))))
             2
  and b3 = test_index_llist_left_to_right_one
             name
             candidate
             "b3"
             show_int
             (Some 3)
             (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil))))))))
             3
  and b4 = test_index_llist_left_to_right_one
             name
             candidate
             "b4"
             show_int
             None
             (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil))))))))
             4
  and b5 = test_index_llist_left_to_right_one
             name
             candidate
             "b4"
             show_int
             None
             (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil))))))))
             ~-1
  in b0 && b1 && b2 && b3 && b4 && b5;;

(* was:
let test_index_llist_left_to_right_int name candidate =
  let b0 = (candidate (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil)))))))) 0 = Some 0)
  and b1 = (candidate (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil)))))))) 1 = Some 1)
  and b2 = (candidate (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil)))))))) 2 = Some 2)
  and b3 = (candidate (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil)))))))) 3 = Some 3)
  and b4 = (candidate (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil)))))))) 4 = None)
  and b5 = (candidate (Lcons (0, lazy (Lcons (1, lazy (Lcons (2, lazy (Lcons (3, lazy Lnil)))))))) ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;
*)

(* Part a *)
let index_llist_left_to_right_v0 vs_given n_given =
  let rec visit lvs a =
    match lvs with
    | Lnil ->
       None
    | Lcons (v, dlvs') ->
       (match a with
        | 0 ->
           Some v
        | _ ->
           visit (Lazy.force dlvs') (pred a))
  in visit vs_given n_given;;


let () = assert (test_index_llist_left_to_right_int "index_llist_left_to_right_v0" index_llist_left_to_right_v0);;

let index_llist_left_to_right_v1 vs_given n_given =
  let rec visit lvs =
    match lvs with
    | Lnil ->
       fun a -> None
    | Lcons (v, dlvs') ->
       fun a -> (match a with
                 | 0 ->
                    Some v
                 | _ ->
                    visit (Lazy.force dlvs') (pred a))
  in visit vs_given n_given;;


let () = assert (test_index_llist_left_to_right_int "index_llist_left_to_right_v1" index_llist_left_to_right_v1);;

(* Part b *)

let index_llist_left_to_right_v2 vs_given n_given =
  fold_right_llist (fun a -> None) (fun v ih a -> if a = 0
                                                  then Some v
                                                  else ih (pred a))
    vs_given n_given;;

let () = assert (test_index_llist_left_to_right_int "index_llist_left_to_right_v2" index_llist_left_to_right_v2);;
                                    

(* Part c *)

let index_llist_left_to_right_v3 vs_given n_given =
 let rec visit n (Lcons (v, ds)) =
   match n with
   | 0 ->
      (match (Lcons (v, ds)) with
       | Lnil ->
          None
       | _ ->
          Some v)
   | _ ->
      (match Lazy.force ds with
       | Lnil ->
          None
       | _ ->
          visit (pred n) (Lazy.force ds))
 in visit n_given vs_given;;
 

let () = assert (test_index_llist_left_to_right_int "index_llist_left_to_right_v3" index_llist_left_to_right_v3);;

let index_llist_left_to_right_v4 vs_given n_given =
 let rec visit n =
   match n with
   | 0 ->
      fun (Lcons (v, ds)) -> (match (Lcons (v, ds)) with
                              | Lnil ->
                                 None
                              | _ ->
                                 Some v)
   | _ ->
      fun (Lcons (v, ds)) -> (match (Lazy.force ds) with
                              | Lnil ->
                                 None
                              | _ ->
                                 visit (pred n) (Lazy.force ds))
 in visit n_given vs_given;;

let () = assert (test_index_llist_left_to_right_int "index_llist_left_to_right_v4" index_llist_left_to_right_v4);;

(* Part d *)

let index_llist_left_to_right_v5 vs_given n_given =
  if 0 <= n_given
  then (fold_right_nat (fun (Lcons (v, ds)) -> (match (Lcons (v, ds)) with
                                                | Lnil ->
                                                   None
                                                | _ ->
                                                   Some v))
          (fun i (Lcons (v, ds)) -> (match (Lazy.force ds) with
                                     | Lnil ->
                                        None
                                     | _ ->
                                        i (Lazy.force ds)))
          n_given vs_given)
  else None;;

let () = assert (test_index_llist_left_to_right_int "index_llist_left_to_right_v5" index_llist_left_to_right_v5);;
 

(* ********** *)

let test_index_llist_right_to_left_one name candidate test show_yourself expected_result given_llist given_index =
  let actual_result = candidate given_llist given_index
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_index_llist_right_to_left failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_option show_yourself actual_result)
                     (show_option show_yourself expected_result)
          in false;;


let fold_right_llist lnil_case lcons_case lvs_init =
 (* fold_right_llist : 'a -> ('b -> 'a -> 'a) -> 'b llist -> 'a *)
  let rec visit lvs =
       (* visit : 'b llist -> 'a *)
    match lvs with
    | Lnil ->
       lnil_case
    | Lcons (v, dlvs') ->
       let ih = visit (Lazy.force dlvs')
       in lcons_case v ih
  in visit lvs_init;;

let fold_left_llist lnil_case lcons_case lvs_init =
 (* fold_left_llist : 'a -> ('b -> 'a -> 'a) -> 'b llist -> 'a *)
  let rec loop lvs a =
    (* loop : 'b llist -> 'a *)
    match lvs with
    | Lnil ->
       a
    | Lcons (v, dlvs') ->
       loop (Lazy.force dlvs') (lcons_case v a)
  in loop lvs_init lnil_case;;

let test_index_llist_right_to_left_int name candidate =
  let b0 = test_index_llist_right_to_left_one
             name
             candidate
             "b0"
             show_int
             (Some 0)
             (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil))))))))
             0
  and b1 = test_index_llist_right_to_left_one
             name
             candidate
             "b1"
             show_int
             (Some 1)
             (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil))))))))
             1
  and b2 = test_index_llist_right_to_left_one
             name
             candidate
             "b2"
             show_int
             (Some 2)
             (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil))))))))
             2
  and b3 = test_index_llist_right_to_left_one
             name
             candidate
             "b3"
             show_int
             (Some 3)
             (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil))))))))
             3
  and b4 = test_index_llist_right_to_left_one
             name
             candidate
             "b4"
             show_int
             None
             (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil))))))))
             4
  and b5 = test_index_llist_right_to_left_one
             name
             candidate
             "b4"
             show_int
             None
             (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil))))))))
             ~-1
  in b0 && b1 && b2 && b3 && b4 && b5;;

(* was:
let test_index_llist_right_to_left_int name candidate =
  let b0 = (candidate (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil)))))))) 0 = Some 0)
  and b1 = (candidate (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil)))))))) 1 = Some 1)
  and b2 = (candidate (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil)))))))) 2 = Some 2)
  and b3 = (candidate (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil)))))))) 3 = Some 3)
  and b4 = (candidate (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil)))))))) 4 = None)
  and b5 = (candidate (Lcons (3, lazy (Lcons (2, lazy (Lcons (1, lazy (Lcons (0, lazy Lnil)))))))) ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;
 *)

(* Part a *)

let index_llist_right_to_left_v0 vs_given n_given =
  let rec visit lvs =
    match lvs with
    | Lnil ->
       (n_given, None)
    | Lcons (v, dlvs') ->
       let (i, x) = visit (Lazy.force dlvs')
       in match i with
          | 0 ->
             (i-1, Some v)
          | _ ->
             (i-1, x)
  in let (_, x) = visit vs_given
     in x;;

let () = assert (test_index_llist_right_to_left_int "index_llist_right_to_left_v0" index_llist_right_to_left_v0);;


(* Part b *)

let index_llist_right_to_left_v1 vs_given n_given =
  let (_, x) = ((fold_right_llist (n_given, None) (fun v ih -> let (i, x) = ih
                                                               in if i = 0
                                                                  then (i-1, Some v)
                                                                  else (i-1, x)))
                  vs_given)
  in x;;
                     
let () = assert (test_index_llist_right_to_left_int "index_llist_right_to_left_v1" index_llist_right_to_left_v1);;


(* ********** *)
(* Indexing Streams *)

let test_index_stream_left_to_right_int candidate =
  let make_stream seed next =
    let rec produce v =
      Scons (v, lazy (produce (next v)))
    in produce seed
  in let b0 = (candidate (make_stream 0 succ) ~-1 = None)
     and b1 = (candidate (make_stream 0 succ) 0 = Some 0)
     and b2 = (candidate (make_stream 0 succ) 2 = Some 2)
     in b0 && b1 && b2;;

(* Part a *)

let index_stream_left_to_right_v0 s_given n_given =
  if n_given < 0
  then None
  else let rec visit (Scons (v, ds)) a =
         match a with
         | 0 ->
            Some v
         | _ ->
            visit (Lazy.force ds) (a-1)
       in visit s_given n_given;;

let () = assert (test_index_stream_left_to_right_int index_stream_left_to_right_v0);;


(* ********** *)

(* Indexing Binary Trees *)
(*
#use "term-project_about-queues.ml";;
 *)
module type QUEUE =
  sig
    type 'a queue
    val empty : 'a queue
    val is_empty : 'a queue -> bool
    val enqueue : 'a -> 'a queue -> 'a queue
    val dequeue : 'a queue -> ('a * 'a queue) option
    val show : ('a -> string) -> 'a queue -> string
  end;;

module Lifo : QUEUE =
  struct
    type 'a queue = 'a list

    let empty = []

    let is_empty q =
      match q with
      | [] ->
         true
      | _ :: _ ->
         false

    let is_empty' q =
      q = []

    let enqueue v q =
      v :: q

    let dequeue q =
      match q with
      | [] ->
         None
      | v :: q' ->
         Some (v, q')

    let show show_yourself q =
      show_list show_yourself q
  end;;


module Fifo : QUEUE =
  struct
    type 'a queue = 'a list * 'a list

    let empty =
      ([], [])

    let is_empty q =
      q = ([], [])

    let enqueue x (pool, reversed_prefix) =
      (pool, x :: reversed_prefix)

    let dequeue (pool, reversed_prefix) =
      match pool with
      | [] ->
         (match List.rev reversed_prefix with
          | [] ->
             None
          | x :: new_pool ->
             Some (x, (new_pool, [])))
      | x :: pool' ->
         Some (x, (pool', reversed_prefix))

    (* rendering Okasaki's representation: *)
    let show show_yourself (pool, reversed_prefix) =
      "(" ^ show_list show_yourself pool ^ ", " ^ show_list show_yourself reversed_prefix ^ ")"

    (* rendering a list representation where the last enqueued element occurs first: *)
    let show show_yourself (pool, reversed_prefix) =
      show_list show_yourself (pool @ List.rev reversed_prefix)
  end;;



let traverse_foo empty enqueue dequeue t =
  let rec process q =
    match dequeue q with
    | None ->
       []
    | Some (t, q') ->
       (match t with
        | Leaf x ->
           x :: process q'
        | Node (t1, t2) ->
           process (enqueue t1 (enqueue t2 q')))
  in process (enqueue t empty);;


let traverse_foo_lifo t =
 (* traverse_foo_lifo : 'a binary_tree -> 'a list *) 
  traverse_foo Lifo.empty Lifo.enqueue Lifo.dequeue t;;



(* ********** *)

(* Part a *)

let test_index_binary_tree_depth_first_left_to_right_int candidate =
  let b0 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 0 = Some 1)
  and b1 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 1 = Some 2)
  and b2 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 2 = Some 3)
  and b3 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 3 = Some 4)
  and b4 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 4 = None)
  and b5 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;



let index_tree_depth_first_left_to_right_v0 t_given n_given =
  index_list_left_to_right_v0 (traverse_foo_lifo t_given) n_given;;


let () = assert (test_index_binary_tree_depth_first_left_to_right_int index_tree_depth_first_left_to_right_v0);; 


let index_tree_depth_first_left_to_right_v1 t_given n_given =
  let rec process q a =
    match Lifo.dequeue q with
    | None ->
       None
    | Some (t, q') ->
       (match t with
        | Leaf x ->
           (match a with
           | n_given ->
              Some x
           | _ ->
              process q' (a + 1))
        | Node (t1, t2) ->
           process (Lifo.enqueue t1 (Lifo.enqueue t2 q')) a) 
  in process (Lifo.enqueue t_given Lifo.empty) 0;;


let index_tree_depth_first_left_to_right_v2 t_given n_given =
  let rec visit t a =
    match t with
    | Leaf v ->
       (match a with
        | 0 ->
           (a, Some v)
        | _ ->
           (a-1, None))
    | Node (t1, t2) ->
      (match visit t1 a with
       | (i, None) ->
          visit t2 i
       | (i, Some v) ->
          (i, Some v))
  in let (_, x) = (visit t_given n_given)
     in x;;

let index_tree_depth_first_left_to_right_v2' t_given n_given =
  let rec visit t a =
    match t with
    | Leaf v ->
       (match a with
        | 0 ->
           Found v
        | _ ->
           Still_looking (a-1))
    | Node (t1, t2) ->
       (match visit t1 a with
       | Still_looking a ->
          visit t2 a
       | Found v ->
          Found v)
  in match (visit t_given n_given) with
     | Found v ->
        Some v
     | _ ->
        None;;

exception Found_it of int;;

let index_tree_depth_first_left_to_right_v2'' t_given n_given =
  let rec visit t a =
    match t with
    | Leaf v ->
       (match a with
        | 0 ->
           raise (Found_it v)
        | _ ->
           (a-1))
    | Node (t1, t2) ->
       (match visit t1 a with
       | i ->
          visit t2 i)
  in try let _ = (visit t_given n_given) in None with
     | Found_it v ->
        Some v;;

let () = assert (test_index_binary_tree_depth_first_left_to_right_int index_tree_depth_first_left_to_right_v2);;

let () = assert (test_index_binary_tree_depth_first_left_to_right_int index_tree_depth_first_left_to_right_v2');;

let () = assert (test_index_binary_tree_depth_first_left_to_right_int index_tree_depth_first_left_to_right_v2'');;

let index_tree_depth_first_left_to_right_v3 t_given n_given =
  let (_, x) = (fold_binary_tree (fun v a -> match a with
                                                  | 0 ->
                                                     (a, Some v)
                                                  | _ ->
                                                     (a-1, None))
                  (fun ih1 ih2 a -> match ih1 a with
                                    | (i, None) ->
                                       ih2 i
                                    | (i, Some v) ->
                                       (i, Some v))
                  t_given n_given)
  in x;;
 
let () = assert (test_index_binary_tree_depth_first_left_to_right_int index_tree_depth_first_left_to_right_v3);;

let index_tree_depth_first_left_to_right_v3' t_given n_given =
  match (fold_binary_tree (fun v a ->  match a with
                                       | 0 ->
                                          Found v
                                       | _ ->
                                          Still_looking (a-1))
           (fun ih1 ih2 a -> match ih1 a with
                             | Still_looking a ->
                                ih2 a
                             | Found v ->
                                Found v)
           t_given n_given) with
  | Found v ->
     Some v
  | _ ->
     None;;

let () = assert (test_index_binary_tree_depth_first_left_to_right_int index_tree_depth_first_left_to_right_v3');;

(* Part b *)

let test_index_binary_tree_depth_first_right_to_left_int candidate =
  let b0 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 0 = Some 4)
  and b1 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 1 = Some 3)
  and b2 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 2 = Some 2)
  and b3 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 3 = Some 1)
  and b4 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 4 = None)
  and b5 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;


let index_tree_depth_first_right_to_left_v0 t_given n_given =
  let rec process q a =
    match Lifo.dequeue q with
    | None ->
       None
    | Some (t, q') ->
       (match t with
        | Leaf x ->
           (match a with
            | 0 ->
               Some x
            | _ ->
               process q' (a-1))
        | Node (t1, t2) ->
           process (Lifo.enqueue t2 (Lifo.enqueue t1 q')) a) 
  in process (Lifo.enqueue t_given Lifo.empty) n_given;;

let () = assert (test_index_binary_tree_depth_first_right_to_left_int index_tree_depth_first_right_to_left_v0);;

let index_tree_depth_first_right_to_left_v1 t_given n_given =
  let rec visit t a =
    match t with
    | Leaf v ->
       (match a with
        | 0 ->
           (a, Some v)
        | _ ->
           (a-1, None))
    | Node (t1, t2) ->
        match visit t2 a with
        | (i, None) ->
           visit t1 i
        | (i, Some v) ->
           (i, Some v)
     in let (_, x) = (visit t_given n_given)
        in x;;

let () = assert (test_index_binary_tree_depth_first_right_to_left_int index_tree_depth_first_right_to_left_v1);;

let index_tree_depth_first_right_to_left_v2 t_given n_given =
  let (_, x) = (fold_binary_tree (fun v a -> match a with
                                             | 0 ->
                                                (a, Some v)
                                             | _ ->
                                                (a-1, None))
                  (fun ih1 ih2 a -> match ih2 a with
                                    | (i, None) ->
                                       ih1 i
                                    | (i, Some v) ->
                                       (i, Some v))
                  t_given n_given)
  in x;;

let () = assert (test_index_binary_tree_depth_first_right_to_left_int index_tree_depth_first_right_to_left_v2);;

let index_tree_depth_first_right_to_left_v1' t_given n_given =
  let rec visit t a =
    match t with
    | Leaf v ->
       (match a with
        | 0 ->
           Found v
        | _ ->
           Still_looking (a-1))
    | Node (t1, t2) ->
       (match visit t2 a with
       | Still_looking a ->
          visit t1 a
       | Found v ->
          Found v)
  in match (visit t_given n_given) with
     | Found v ->
        Some v
     | _ ->
        None;;

let () = assert (test_index_binary_tree_depth_first_right_to_left_int index_tree_depth_first_right_to_left_v1');;

let index_tree_depth_first_right_to_left_v2' t_given n_given =
  match (fold_binary_tree (fun v a ->  match a with
                                       | 0 ->
                                          Found v
                                       | _ ->
                                          Still_looking (a-1))
           (fun ih1 ih2 a -> match ih2 a with
                             | Still_looking a ->
                                ih1 a
                             | Found v ->
                                Found v)
           t_given n_given) with
  | Found v ->
     Some v
  | _ ->
     None;;

let () = assert (test_index_binary_tree_depth_first_right_to_left_int index_tree_depth_first_right_to_left_v2');;

let index_tree_depth_first_right_to_left_v1'' t_given n_given =
  let rec visit t a =
    match t with
    | Leaf v ->
       (match a with
        | 0 ->
           raise (Found_it v)
        | _ ->
           (a-1))
    | Node (t1, t2) ->
       (match visit t2 a with
       | i ->
          visit t1 i)
  in try let _ = (visit t_given n_given) in None with
     | Found_it v ->
        Some v;;

let () = assert (test_index_binary_tree_depth_first_right_to_left_int index_tree_depth_first_right_to_left_v1'');;

(* Part c *)

let test_index_binary_tree_breadth_first_left_to_right_int candidate =
  let b0 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 0 = Some 1)
  and b1 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 1 = Some 4)
  and b2 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 2 = Some 2)
  and b3 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 3 = Some 3)
  and b4 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 4 = None)
  and b5 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;


let index_tree_breadth_first_left_to_right_v0 t_given n_given =
  let rec process q a =
    match Fifo.dequeue q with
    | None ->
       None
    | Some (t, q') ->
       (match t with
        | Leaf x ->
           (match a with
           | 0 ->
              Some x
           | _ ->
              process q' (a-1))
        | Node (t1, t2) ->
           process (Fifo.enqueue t2 (Fifo.enqueue t1 q')) a) 
  in process (Fifo.enqueue t_given Fifo.empty) n_given;;

let () = assert (test_index_binary_tree_breadth_first_left_to_right_int index_tree_breadth_first_left_to_right_v0);;

(* Part d *)

let test_index_binary_tree_breadth_first_right_to_left_int candidate =
  let b0 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 0 = Some 1)
  and b1 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 1 = Some 4)
  and b2 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 2 = Some 3)
  and b3 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 3 = Some 2)
  and b4 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) 4 = None)
  and b5 = (candidate (Node (Leaf 1, Node (Node (Leaf 2, Leaf 3), Leaf 4))) ~-1 = None)
  in b0 && b1 && b2 && b3 && b4 && b5;;


let index_tree_breadth_first_right_to_left_v0 t_given n_given =
  let rec process q a =
    match Fifo.dequeue q with
    | None ->
       None
    | Some (t, q') ->
       (match t with
        | Leaf x ->
           (match a with
            | 0 ->
               Some x
            | _ ->
               process q' (a-1))
        | Node (t1, t2) ->
           process (Fifo.enqueue t1 (Fifo.enqueue t2 q')) a) 
  in process (Fifo.enqueue t_given Fifo.empty) n_given;;

let () = assert (test_index_binary_tree_breadth_first_right_to_left_int index_tree_breadth_first_right_to_left_v0);;


(* ********** *)
(* end of term-project_about-indexing-data-structures.ml *)
