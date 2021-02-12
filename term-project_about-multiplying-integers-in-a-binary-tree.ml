
(* term-project_about-multiplying-integers-in-a-binary-tree.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2019-2020 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Sun 05 Apr 2020 *)

exception Zero;;


let repeat n_given thunk =
  assert (n_given >= 0);
  let rec loop n =
    if n = 0
    then true
    else thunk () && loop (pred n)
  in loop n_given;;

let show_int n =
  if n < 0
  then "(" ^ string_of_int n ^ ")"
  else string_of_int n;;

(* ********** *)

type 'a binary_tree =
  | Leaf of 'a
  | Node of 'a binary_tree * 'a binary_tree;;

let show_binary_tree show_yourself t =
  let rec visit t =
    match t with
    | Leaf v ->
       "Leaf " ^ (show_yourself v)
    | Node (t1, t2) ->
       "Node (" ^ visit t1 ^ ", " ^ visit t2 ^ ")"
  in visit t;;

let fold_binary_tree leaf_case node_case t_given =
  let rec visit t =
    match t with
    | Leaf v ->
       leaf_case v
    | Node (t1, t2) ->
       node_case (visit t1) (visit t2)
  in visit t_given;;

let generate_random_binary_tree_int d_given =
  let rec generate d =
    if d = 0
    then Leaf (Random.int 5)
    else match Random.int 3 with
         | 0 ->
            Leaf (- (Random.int 5))
         | _ ->
            let d' = pred d
            in Node (generate d', generate d')
  in generate d_given;;

(* ********** *)

let test_mult_one name candidate test expected_result given_tree =
  let actual_result = candidate given_tree
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_mult failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_binary_tree show_int given_tree)
                     (show_int expected_result)
          in false;;

let mult_witness t_given =
  let rec visit t =
    match t with
    | Leaf n ->
       n
    | Node (t1, t2) ->
       visit t1 * visit t2
  in visit t_given;;

let test_mult name candidate_mult =
  let b0 = test_mult_one name candidate_mult "b0" 0 (Leaf 0)
  and b1 = test_mult_one name candidate_mult "b1" 1 (Leaf 1)
  and b2 = test_mult_one name candidate_mult "b2" 2 (Node (Leaf 1,
                                                           Leaf 2))
  and b3 = test_mult_one name candidate_mult "b3" 6 (Node (Leaf 1,
                                                           Node (Leaf 2,
                                                                 Leaf 3)))
  and b4 = test_mult_one name candidate_mult "b4" 24 (Node (Leaf 1,
                                                            Node (Leaf 2,
                                                                  Node (Leaf 3,
                                                                        Leaf 4))))
  and b5 = test_mult_one name candidate_mult "b5" 120 (Node (Leaf 1,
                                                             Node (Leaf 2,
                                                                   Node (Leaf 3,
                                                                         Node (Leaf 4,
                                                                               Leaf 5)))))
  and b6 = test_mult_one name candidate_mult "b6" 0 (Node (Leaf 1,
                                                           Node (Leaf 2,
                                                                 Node (Leaf 0,
                                                                       Node (Leaf 4,
                                                                             Leaf 5)))))
  and b7 = test_mult_one name candidate_mult "b7" 0 (Node (Node (Node (Leaf 1,
                                                                       Leaf 2),
                                                                 Node (Leaf 3,
                                                                       Leaf 0)),
                                                           Node (Leaf 4,
                                                                 Leaf 5)))
  and b8 = let thunk = (fun () -> let t = generate_random_binary_tree_int 10
                                  in test_mult_one name candidate_mult "b8" (mult_witness t) t)
           in repeat 4 thunk

  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8;;

let () = assert (test_mult "mult_witness" mult_witness);;

(* ********** *)

exception Zero;;

let mult_v5 t_given =
  let rec visit t =
    match t with
    | Leaf n ->
       if n = 0
       then raise Zero
       else n
    | Node (t1, t2) ->
       visit t1 * visit t2
  in try visit t_given with
     | Zero ->
        0;;

let () = assert (test_mult "mult_v5" mult_v5);;

(* ********** *)

(* using an accumulator and no exception: *)

(* use accumulator in place of the continution function so that we can bypass the option type *)

let mult_v7 t_given =
  let rec visit t a =
    match t with
    | Leaf n ->
       a * n
    | Node (t1, t2) ->
       visit t1 (visit t2 a)
  in visit t_given 1;;

let () = assert (test_mult "mult_v7" mult_v7);;

(* ***** *)

(* the fold_binary_tree version, still using an accumulator and no exception *)

(*the intermediate steps are shown and explained in details in the report *)

let mult_v7_alt t_given =
  fold_binary_tree
    (fun n a -> a * n)
    (fun ih1 ih2 a -> ih1 (ih2 a))
    t_given 1;;

let () = assert (test_mult "mult_v7_alt" mult_v7_alt);;

(* ********** *)

(* using an accumulator and an exception *)

let mult_v8 t_given =
  let rec visit t a =
    try
      match t with
      | Leaf n ->
         if n = 0
         then raise Zero
         else a * n
      | Node (t1, t2) ->
         visit t1 (visit t2 a)
    with
    | Zero -> 0
  in visit t_given 1;;


let () = assert (test_mult "mult_v8" mult_v8);;


(* ***** *)

(* the fold_binary_tree version, using an accumulator and an exception *)

let mult_v8_alt t_given =
  try fold_binary_tree
	(fun n a -> if n = 0 then raise Zero else a * n)
	(fun ih1 ih2 a -> ih1 (ih2 a))
	t_given 1
  with
  |Zero -> 0;;


let () = assert (test_mult "mult_v8_alt" mult_v8_alt);;


(*

Based on Prof Danvy's comments, we produced and compared the traces of our mult_v7 and the model function mult_witness:

let mult_witness_tracing t_given =
  let rec visit t =
    Printf.printf "%s ->\n" (show_binary_tree show_int t);
    match t with
    | Leaf n ->
       n
    | Node (t1, t2) ->
       visit t1 * visit t2
  in visit t_given;;

let mult_v7_tracing t_given =
  let rec visit t a =
    Printf.printf "%s ->\n" (show_binary_tree show_int t);
    match t with
    | Leaf n ->
       if n = 0
       then 0
       else a * n
    | Node (t1, t2) ->
       visit t1 (visit t2 a)
  in visit t_given 1;;

let t = generate_random_binary_tree_int 4;;

mult_witness_tracing (t);;

mult_v7_tracing (t);;

# mult_witness_tracing (t);;
Node (Node (Leaf (-1), Node (Leaf (-2), Node (Leaf 2, Leaf 4))), Node (Leaf (-1), Node (Node (Leaf 4, Leaf 2), Node (Leaf 3, Leaf 4)))) ->
Node (Leaf (-1), Node (Node (Leaf 4, Leaf 2), Node (Leaf 3, Leaf 4))) ->
Node (Node (Leaf 4, Leaf 2), Node (Leaf 3, Leaf 4)) ->
Node (Leaf 3, Leaf 4) ->
Leaf 4 ->
Leaf 3 ->
Node (Leaf 4, Leaf 2) ->
Leaf 2 ->
Leaf 4 ->
Leaf (-1) ->
Node (Leaf (-1), Node (Leaf (-2), Node (Leaf 2, Leaf 4))) ->
Node (Leaf (-2), Node (Leaf 2, Leaf 4)) ->
Node (Leaf 2, Leaf 4) ->
Leaf 4 ->
Leaf 2 ->
Leaf (-2) ->
Leaf (-1) ->
- : int = -1536

-----------
Trace when the node case is:
 | Node (t1, t2) ->
       visit t2 (visit t1 a)

# mult_v7_tracing (t);;
Node (Node (Leaf (-1), Node (Leaf (-2), Node (Leaf 2, Leaf 4))), Node (Leaf (-1), Node (Node (Leaf 4, Leaf 2), Node (Leaf 3, Leaf 4)))) ->
Node (Leaf (-1), Node (Leaf (-2), Node (Leaf 2, Leaf 4))) ->
Leaf (-1) ->
Node (Leaf (-2), Node (Leaf 2, Leaf 4)) ->
Leaf (-2) ->
Node (Leaf 2, Leaf 4) ->
Leaf 2 ->
Leaf 4 ->
Node (Leaf (-1), Node (Node (Leaf 4, Leaf 2), Node (Leaf 3, Leaf 4))) ->
Leaf (-1) ->
Node (Node (Leaf 4, Leaf 2), Node (Leaf 3, Leaf 4)) ->
Node (Leaf 4, Leaf 2) ->
Leaf 4 ->
Leaf 2 ->
Node (Leaf 3, Leaf 4) ->
Leaf 3 ->
Leaf 4 ->
- : int = -1536

We then realized that our function is traversing from left to right, but the other model function is from right to left. 

----------
Trace after changing the order of t1 and t2, i.e., when the node case is:
 | Node (t1, t2) ->
       visit t1 (visit t2 a)

# mult_v7_tracing (t);;
Node (Node (Leaf (-1), Node (Leaf (-2), Node (Leaf 2, Leaf 4))), Node (Leaf (-1), Node (Node (Leaf 4, Leaf 2), Node (Leaf 3, Leaf 4)))) ->
Node (Leaf (-1), Node (Node (Leaf 4, Leaf 2), Node (Leaf 3, Leaf 4))) ->
Node (Node (Leaf 4, Leaf 2), Node (Leaf 3, Leaf 4)) ->
Node (Leaf 3, Leaf 4) ->
Leaf 4 ->
Leaf 3 ->
Node (Leaf 4, Leaf 2) ->
Leaf 2 ->
Leaf 4 ->
Leaf (-1) ->
Node (Leaf (-1), Node (Leaf (-2), Node (Leaf 2, Leaf 4))) ->
Node (Leaf (-2), Node (Leaf 2, Leaf 4)) ->
Node (Leaf 2, Leaf 4) ->
Leaf 4 ->
Leaf 2 ->
Leaf (-2) ->
Leaf (-1) ->
- : int = -1536

*)

(* ********** *)

(* end of term-project_about-multiplying-integers-in-a-binary-tree.ml *)

