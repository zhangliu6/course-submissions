(* term-project_about-the-knapsack-problem.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2019-2020 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Sat 04 Apr 2020 *)

(* ********** *)

(* name: Liu Chengpei
   email address: liuchengpei96@u.yale-nus.edu.sg       
   student number: A0136151R
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

let powerset given_vs =
  let rec outer_visit vs =
    match vs with
    | [] ->
       [[]]
    | v :: vs' ->
       let outer_ih = outer_visit vs'
       in let rec inner_visit wss =
            match wss with
            | [] ->
               outer_ih
            | ws :: wss' ->
               let inner_ih = inner_visit wss'
               in (v :: ws) :: inner_ih
          in inner_visit outer_ih
  in outer_visit given_vs;;

let assess_subset given_triples =
  let rec loop triples total_weight total_monetary_value =
    match triples with
    | [] ->
       (total_weight, total_monetary_value, given_triples)
    | (name, weight, monetary_value) :: triples' ->
       loop triples' (total_weight + weight) (total_monetary_value + monetary_value)
  in loop given_triples 0 0;;

let assess_powerset given_tripless =
  List.map assess_subset given_tripless;;

let filter_out p given_vs =
  let rec visit vs =
    match vs with
    | [] ->
       []
    | v :: vs' ->
       if p v
       then visit vs'
       else v :: visit vs'
  in visit given_vs;;

let minimize_the_weight given_weight assessed_subsets =
  filter_out
    (fun (weight, monetary_value, triples) ->
      weight > given_weight)
    assessed_subsets;;

type comparison = Lt | Eq | Gt;;

let compare v1 v2 =
  if v1 < v2 then Lt else if v1 = v2 then Eq else Gt;;

let maximize_the_monetary_value given_candidate_subsets =
  let rec visit candidate_subsets =
    match candidate_subsets with
    | [] ->
       (0, [])
    | candidate_subset :: candidate_subsets' ->
       let (weight, monetary_value, triples) = candidate_subset
       and (current_monetary_value, current_candidate_subsets) = visit candidate_subsets'
       in match compare monetary_value current_monetary_value with
          | Lt ->
             (current_monetary_value, current_candidate_subsets)
          | Eq ->
             (current_monetary_value, candidate_subset :: current_candidate_subsets)
          | Gt ->
             (monetary_value, candidate_subset :: [])
  in visit given_candidate_subsets;;

let minimax_v0 given_weight given_triples =
  maximize_the_monetary_value
    (minimize_the_weight
       given_weight
       (List.map
          assess_subset
          (powerset given_triples)));;

let test_minimax candidate =
   let b0 = (candidate 2 [("diamond", 10, 100); ("ruby1", 7, 70); ("ruby2", 7, 70); ("jade", 3, 30)]  = (0, [(0, 0, [])]))
   and b1 = (candidate 5 [("diamond", 10, 100); ("ruby1", 7, 70); ("ruby2", 7, 70); ("jade", 3, 30)] = (30, [(3, 30, [("jade", 3, 30)])]))
   and b2 = (candidate 8 [("diamond", 10, 100); ("ruby1", 7, 70); ("ruby2", 7, 70); ("jade", 3, 30)] = (70, [(7, 70, [("ruby1", 7, 70)]); (7, 70, [("ruby2", 7, 70)])]))
   and b3 = (candidate 10 [("diamond", 10, 100); ("ruby1", 7, 70); ("ruby2", 7, 70); ("jade", 3, 30)] = (100, [(10, 100, [("diamond", 10, 100)]); (10, 100, [("ruby1", 7, 70); ("jade", 3, 30)]); (10, 100, [("ruby2", 7, 70); ("jade", 3, 30)])]))
   in b0 && b1 && b2 && b3;;



(* ********** *)

let minimize_assessed_powerset_v0 given_weight given_triples =
  minimize_the_weight
    given_weight
    (List.map
       assess_subset
       (powerset given_triples));;

let minimax_v0_alt given_weight given_triples =
  maximize_the_monetary_value
    (minimize_assessed_powerset_v0 given_weight given_triples);;

let () = assert(test_minimax minimax_v0);;

(* ********** *)

let minimize_assessed_powerset_v1  given_weight given_vs =
  let rec outer_visit vs =
    match vs with
    | [] ->
       [(0,0,[])]
    | (v,weight1,monetary_value1) :: vs' ->
       let outer_ih = outer_visit vs'
       in let rec inner_visit wss =
            match wss with
            | [] ->
               outer_ih
            | (weight2,monetary_value2, ws) :: wss' ->
               let inner_ih = inner_visit wss'
               in if (weight1+weight2 ) <=given_weight
                  then ( weight1+ weight2, monetary_value1+monetary_value2,(v,weight1,monetary_value1) :: ws) :: inner_ih
                  else inner_ih
          in inner_visit outer_ih
  in outer_visit given_vs;;


let minimax_v1 given_weight given_triples =
  maximize_the_monetary_value
    (minimize_assessed_powerset_v1 given_weight given_triples);;

let () = assert(test_minimax minimax_v1);;


(*Let us use fold_right_list*)

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

let minimize_assessed_powerset_v2  given_weight given_vs =
  let cons_case1 v ih =
    let (v1, weight1, monetary_value1)=v
    in let cons_case2 v' ih' =
         let (weight2, monetary_value2,v2)=v'
         in if (weight1+weight2 ) <=given_weight
                  then (weight1+ weight2, monetary_value1+monetary_value2,(v1,weight1,monetary_value1) :: v2) :: ih'
                  else ih'
       in fold_right_list ih cons_case2 ih
  in fold_right_list [(0,0,[])] cons_case1 given_vs;;

let minimax_v2 given_weight given_triples =
  maximize_the_monetary_value
    (minimize_assessed_powerset_v2 given_weight given_triples);;

let () = assert(test_minimax minimax_v2);;

(* end of term-project_about-the-knapsack-problem.ml *)
