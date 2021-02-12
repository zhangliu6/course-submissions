(*Jincong Chu, Zhi Yi Yeo, Chengpei Liu, Liu Zhang *)
(* Intro to CS Mini-project: The case of the Fibonacci numbers*)

(* liu-fibonacci.ml *)
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


(*Exercise 1*)
(* ------ Preliminaries ------- *)
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

(* ------ Unit Test for fib ------ *)

let test_fib candidate =
      (* base cases: *)
  let b0 = (candidate 0 = 0)
  and b1 = (candidate 1 = 1)
      (* intuitive numbers: *)
  and b2 = (candidate 2 = 1)
  and b3 = (candidate 3 = 2)
  and b4 = (candidate 4 = 3)
  and b5 = (candidate 5 = 5)
  and b6 = (candidate 6 = 8)
      (* instance of the induction step: *)
  and b7 = (let n = Random.int 25
            in candidate n + candidate (n + 1) = candidate (n + 2))
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7;;

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

(* ------ We now rewrite the given function fib_v5 using fold_right_nat. ------*)
let fib_v6_0 n_given =
      (* base cases: *)
  let () = assert (n_given >= 0) in
  let (fib_n, fib_succ_n) = fold_right_nat (0, 1) (fun ih -> let (fib_n', fib_n) = ih in (fib_n, fib_n' + fib_n)) n_given
in fib_n;;

let () = assert(test_fib fib_v6_0);;

(* Further simplifying: *)
let fib_v6 n_given =
    let () = assert (n_given >= 0) in
  let (fib_n, fib_succ_n) = fold_right_nat (0, 1) (fun (fib_n', fib_n) -> (fib_n, fib_n' + fib_n)) n_given
  in fib_n;;

let () = assert(test_fib fib_v6);;


(*Exercise 2*)

(*
# traced_fib_v0 4;;
fib_v0 4 ->
  visit 4 ->
    visit 2 ->
      visit 0 ->
      visit 0 <- 0
      visit 1 ->
      visit 1 <- 1
    visit 2 <- 1
    visit 3 ->
      visit 1 ->
      visit 1 <- 1
      visit 2 ->
        visit 0 ->
        visit 0 <- 0
        visit 1 ->
        visit 1 <- 1
      visit 2 <- 1
    visit 3 <- 2
  visit 4 <- 3
fib_v0 4 <- 3
- : int = 3

# traced_fib_v4 4;;
fib_v4 4 ->
  visit 4 ->
    visit 3 ->
      visit 2 ->
        visit 1 ->
        visit 1 <- 1
        visit 0 ->
        visit 0 <- 0
      visit 2 <- 1
      visit 1 ->
      visit 1 <- 1
    visit 3 <- 2
    visit 2 ->
      visit 1 ->
      visit 1 <- 1
      visit 0 ->
      visit 0 <- 0
    visit 2 <- 1
  visit 4 <- 3
fib_v4 4 <- 3
- : int = 3
*)


(* An extra fun experiment with fibonacci function, credit to peer tutor Stinson *)
(*
let fib i =
  let (result, _, _) =
  let rec visit (x, y, i) =
    if i = 0
    then (x, y, i)
    else visit (y, x + y, i - 1)
  in visit (0, 1, i)
  in result;;
 *)

(* end of liu-fibonacci.ml *)
