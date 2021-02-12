(* term-project_about-computing-the-width-of-a-binary-tree.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2019-2020 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Sat 04 Apr 2020 *)

(* ********** *)

(*
   name: Liu Chengpei
   student ID number: A0136151R
   e-mail address: liuchengpei96@u.yale-nus.edu.sg
*)

(*
   name: Jincong Chu
   student ID number: A0156290E
   e-mail address: chu.jincong@u.yale-nus.edu.sg
*)

(*
   name: Zhi Yi Yeo
   student ID number: A0156253H
   e-mail address:zhiyi.yeo@u.yale-nus.edu.sg
*)

(*
   name: Liu Zhang
   student ID number: A0190879J
   e-mail address: zhangliu@u.yale-nus.edu.sg
*)

(* ********** *)

let show_int n =
  if n < 0
  then "(" ^ string_of_int n ^ ")"
  else string_of_int n;;

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

exception Not_implemented_yet of string;;

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

let generate_random_binary_tree_int d_given =
  let rec generate d =
    if d = 0
    then Leaf (Random.int 100)
    else match Random.int 3 with
         | 0 ->
            Leaf (- (Random.int 100))
         | _ ->
            let d' = pred d
            in Node (generate d', generate d')
  in generate d_given;;

let depth t_given =
  let rec visit t =
    match t with
    | Leaf _ ->
       0
    | Node (t1, t2) ->
       succ (max (visit t1) (visit t2))
  in visit t_given;;

(* ********** *)

let width_v0 t_given =
 (* width_v0 : 'a binary_tree -> int *)
  let n = succ (depth t_given)
  in let a = Array.make n 0
     in let rec visit t d =
          Array.set a d (succ (Array.get a d));
          match t with
          | Leaf _ ->
             ()
          | Node (t1, t2) ->
             let d' = succ d
             in visit t1 d';
                visit t2 d'
        in visit t_given 0;
           let rec array_max i m =
             if i = n
             then m
             else array_max (succ i) (max m (Array.get a i))
           in array_max 1 (Array.get a 0);;

(* ********** *)

let mirror t_init =
  let rec mirror_mirror t =
    match t with
    | Leaf n ->
       Leaf n
    | Node (t1, t2) ->
       let ih2 = mirror_mirror t2
       and ih1 = mirror_mirror t1
       in Node (ih2, ih1)
  in mirror_mirror t_init;;

let distorted_mirror_int t =
 (* distorted_mirror_int : int binary_tree -> int binary_tree *)
 let rec visit t =
    match t with
    | Leaf n ->
       Leaf (if Random.bool ()
             then n
             else -n)
    | Node (t1, t2) ->
       let ih2 = visit t2
       and ih1 = visit t1
       in Node (ih2, ih1)
 in visit t;;

let map_binary_tree f t =
 (* map_binary_tree : ('a -> 'b) -> 'a binary_tree -> 'b binary_tree *)
  let rec visit t =
    match t with
    | Leaf v ->
       Leaf (f v)
    | Node (t1, t2) ->
       Node (visit t1, visit t2)
  in visit t;;


(* ********** *)


let test_width_int_one name candidate test expected_result given_tree =
  let actual_result = candidate given_tree
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_width_int failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_binary_tree show_int given_tree)
                     (show_int expected_result)
          in false;;

let test_width_int name candidate_width =
 (* test_width_int : string -> (int binary_tree -> int) -> bool *)
  let b0 = test_width_int_one name candidate_width "b0" 1 (Leaf 1)
  and b1 = test_width_int_one name candidate_width "b1" 2 (Node (Leaf 1,
                                                                 Leaf 2))
  and b2 = test_width_int_one name candidate_width "b2" 2 (Node (Leaf 1,
                                                                 Node (Leaf 1,
                                                                       Leaf 2)))
  and b3 = test_width_int_one name candidate_width "b3" 2 (Node (Node (Leaf 1,
                                                                       Leaf 2),
                                                                 Leaf 2))
  and b4 = test_width_int_one name candidate_width "b4" 4 (Node (Node (Leaf 1,
                                                                       Leaf 2),
                                                                 Node (Leaf 3,
                                                                       Leaf 4)))
  and b5 = test_width_int_one name candidate_width "b5" 6 (Node (Node (Node (Leaf 1,
                                                                             Leaf 2),
                                                                       Leaf 2),
                                                                 Node (Node (Leaf 3,
                                                                             Leaf 4),
                                                                       Node (Leaf 5,
                                                                             Leaf 6))))
  and b6 = test_width_int_one name candidate_width "b6" 6 (Node (Node (Node (Node (Leaf 1,
                                                                                   Leaf 2),
                                                                             Leaf 2),
                                                                       Leaf 2),
                                                                 Node (Node (Leaf 3,
                                                                             Node (Leaf 3,
                                                                                   Leaf 4)),
                                                                       Node (Leaf 5,
                                                                             Leaf 6))))
  and b7 = (let t = generate_random_binary_tree_int 10
            in test_width_int_one
                 name
                 candidate_width
                 "b7"
                 (width_v0 t)
                 t)
             (* etc. *)
  and b8 = (let t = generate_random_binary_tree_int 10
            in test_width_int_one
                 name
                 candidate_width
                 "b8"
                 (candidate_width (mirror t))
                 t
           )
  and b9 = (let t = generate_random_binary_tree_int 10
            in test_width_int_one
                 name
                 candidate_width
                 "b9"
                 (candidate_width (distorted_mirror_int t))
                 t
           )
  and b10 = (let t = generate_random_binary_tree_int 10
            in test_width_int_one
                 name
                 candidate_width
                 "b10"
                 (candidate_width (map_binary_tree succ t))
                 t
           )
  in b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8 && b9 && b10;;

(* ********** *)


let width_v1 t =
  (* width_v1 : 'a binary_tree -> int *)
  let rec sum_queue x1 x2 =
      match x1 with
      | [] ->
         x2
      | v1 :: vs1 ->
         match x2 with
         | [] ->
            x1
         | v2 :: vs2 ->
            v1+v2 :: (sum_queue vs1 vs2)
  in let rec visit t =
    1 :: match t with
    | Leaf v ->
       []
    | Node (t1, t2) ->
       sum_queue (visit t1) (visit t2)
  in let rec list_max max m =
    match m with
    | [] ->
       max
    | i :: m' ->
       if i>max then list_max i m' else list_max max m'
    in list_max 1 (visit t);;

(* ********** *)

let width_v2 t =
 (* width_v2 : 'a binary_tree -> int *)
  let node_case x1 x2 =
    let rec sum_queue x1 x2 =
      match x1 with
      | [] ->
         x2
      | v1 :: vs1 ->
         match x2 with
         | [] ->
            x1
         | v2 :: vs2 ->
            v1+v2 :: (sum_queue vs1 vs2)
    in 1 :: (sum_queue x1 x2)
  in let rec list_max max m =
    match m with
    | [] ->
       max
    | i :: m' ->
       if i>max then list_max i m' else list_max max m'
    in list_max 1 (fold_binary_tree (fun x -> [1])  node_case t);;

let fold_right_list nil_case cons_case vs_init =
 (* fold_right_list : 'a -> ('b -> 'a -> 'a) -> 'b list -> 'a *)
  let rec traverse vs =
       (* traverse : 'b list -> 'a *)
    match vs with
    | [] ->
       nil_case
    | v :: vs' ->
       let ih = traverse vs'
       in cons_case v ih
  in traverse vs_init;;

(*note that we can only use fold_right_list to represent list_max but not sum_queue, because sum_queue takes in two lists*)

let width_v3 t =
  let node_case x1 x2 =
    let rec sum_queue x1 x2 =
      match x1 with
      | [] ->
         x2
      | v1 :: vs1 ->
         match x2 with
         | [] ->
            x1
         | v2 :: vs2 ->
            v1+v2 :: (sum_queue vs1 vs2)
    in 1 :: (sum_queue x1 x2)
  in let list_max m =
       fold_right_list 0 (fun x y -> max x y) m
    in list_max (fold_binary_tree (fun x -> [1])  node_case t);;

(* ********** *)

let () = assert (test_width_int "width_v0" width_v0);;

let () = assert (test_width_int "width_v1" width_v1);;

let () = assert (test_width_int "width_v2" width_v2);;

let () = assert (test_width_int "width_v2" width_v3);;

(* ********** *)

(* end of term-project_about-computing-the-width-of-a-binary-tree.ml *)
