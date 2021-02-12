(*Jincong Chu, Zhi Yi Yeo, Chengpei Liu, Liu Zhang *)
(* Intro to CS Mini-project: A miscellany of recursive programs *)

(* liu-recursion.ml *)
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

(* ------The Preliminaries------ *)

let make_parity_predicate zero_case n_given =
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then zero_case
    else not (visit (pred n))
  in visit n_given;;

let evenp = make_parity_predicate true;;

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

let parafold_right_nat zero_case succ_case n_given =
 (* parafold_right_nat : 'a -> (int -> 'a -> 'a) -> int -> 'a *)
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then zero_case
    else let n' = n - 1
         in let ih = visit n'
            in succ_case n' ih    (* <-- succ_case takes two arguments *)
  in visit n_given;;

(* ------Exercise 3: Factorial in fold_right_nat------ *)
let test_fact candidate =
  let b0 = (candidate 0 = 1)
  and b1 = (candidate 1 = 1)
  and b2 = (candidate 2 = 2)
  and b3 = (candidate 3 = 6)
  and b4 = (let n = 1 + Random.int 20 in candidate (succ n) = candidate n * (succ n))
  in b0 && b1 && b2 && b3 && b4;;

(* Group code: a working function, but perhaps too similar to parafold *)

(* Chengpei's solution *)
let fact_v0 n_given =
  let () = assert (n_given >= 0) in
  let succ_case ih =
    let (ind, factor) = ih
      in (ind + 1, factor * (ind + 1))
  in let (index, factorial) = fold_right_nat (0, 1) succ_case n_given
  in factorial;;

let () = assert(test_fact fact_v0);;

(* unfolding the declaration of ih *)
let fact_v0_1 n_given =
  let () = assert (n_given >= 0) in
  let succ_case (ind, factor) = (ind + 1, factor * (ind + 1))
  in let (index, factorial) = fold_right_nat (0, 1) succ_case n_given
  in factorial;;

let () = assert(test_fact fact_v0_1);;

(* unfolding the declaration of succ_case *)
let fact_v0_2 n_given =
  let () = assert (n_given >= 0) in
  let (index, factorial) = fold_right_nat (0, 1) (fun (ind, factor) -> (ind + 1, factor * (ind + 1))) n_given
  in factorial;;

let () = assert(test_fact fact_v0_2);;

(* My solution: 'remember' only two nearest factorials at each step; inspired by Fibonacci numbers *)

let fact_v1 n_given =
  let () = assert (n_given >= 0) in
  let (fact_n, fact_succ_n) = fold_right_nat (1, 1) (fun ih -> let(fact_n', fact_n) = ih in (fact_n, fact_n * (fact_n/fact_n' + 1))) n_given
  in fact_n;;

let () = assert(test_fact fact_v1);;

(* 
Compare the two:
- we remember different things: for CP, the current term to be multiplied to the preceding factorial; for me, at every point I always remember two nearest factorials.
- same computational complexity
*)

(* ------Exercise 4------*)

let test_sumtorial candidate =
  let b0 = (candidate 0 = 0)
  and b1 = (candidate 1 = 1)
  and b2 = (candidate 2 = 3)
  and b3 = (let n = Random.int 20
		in candidate (succ n) = (succ n) + candidate n)
  in b0 && b1 && b2 && b3;;

let fake_sumtorial n = 
  if n > 0 && n <= 20 then (0 + n) * (n + 1) / 2
  else 0;;

let sumtorial_v1 n_given =
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then 0
    else let n' = pred n
         in let ih = visit n'
            in (succ n') + ih
  in visit n_given;;

let () = assert (test_sumtorial sumtorial_v1);;

let sumtorial_v2 n_given =
  (1 + n_given) * n_given / 2;;

  let () = assert (test_sumtorial sumtorial_v2);;

let sumtorial_v3 n_given =
  let () = assert (n_given >= 0) in
  parafold_right_nat 0 (fun n' ih -> succ(n') + ih) n_given;;

 let () = assert (test_sumtorial sumtorial_v3);;

 
(* We can also define sumtorial using structural recursion fold_right *) 
let sumtorial_v4 n_given =
  let () = assert (n_given >= 0) in
  let (index, sumtorial) = fold_right_nat (1,0) (fun (ind, sum) -> (ind + 1, sum + ind)) n_given
  in sumtorial;;

let () = assert (test_sumtorial sumtorial_v4);;

(* ------- Exercise 5 ------ *)

(* Part a *)
let test_sum candidate f =
  let b0 = (candidate f 0 = f 0)
  and b1 = (candidate f 1 = candidate f 0 + f 1)
  and b2 = (candidate f 2 = candidate f 1 + f 2)
  and b3 = (let n = 1 + Random.int 20
      	    in (candidate f n = candidate f (n-1) + f n))
  and b4 = (let n = Random.int 20
            in (candidate f (n+1) = candidate f n + f (n+1)))
  in b0 && b1 && b2 && b3 && b4;;


let sum_bugged f n_given =
  let () = assert(n_given >= 0) in
  if n_given <= 21
  then let rec visit f n =
         if n = 0
         then f 0
         else let n' = pred n
    	      in let ih = visit f n'
                 in ih + f (succ n')
       in visit f n_given
  else 42;;

let () = assert (test_sum sum_bugged sumtorial_v1);;

(* Part b *)
let sum_v1 f n_given =
  let () = assert(n_given >= 0) in
  let rec visit f n =
    if n = 0
    then f 0
    else let n' = pred n
    	 in let ih = visit f n'
	    in ih + f (succ n')
  in visit f n_given;;

(* Part c *)
let () = assert(test_sum sum_v1 sumtorial_v1);;

(* Part d *)
let sum_v2 f n_given =
  let () = assert(n_given >= 0) in
  parafold_right_nat (f 0) (fun  n' ih -> (f (succ n')) + ih) n_given;;

let () = assert(test_sum sum_v2 sumtorial_v1);;
  
(* Part e *)
let sumtorial_v4 n_given =
  let () = assert (n_given >= 0) in
  sum_v2 (fun x -> x) n_given;;

let () = assert(test_sumtorial sumtorial_v4);;

(* Part f *)
let test_oddsum candidate =
  let b0 = (candidate 0 = 1)
  and b1 = (candidate 1 = 4)
  and b2 = (candidate 2 = 9)
  and b3 = (candidate 3 = 16)
  and b4 = (let n = 1+ Random.int 20 in
            (candidate n = candidate (n-1) + (2 * n + 1)))
in b0 && b1 && b2 && b3 && b4;;


let oddsum_v1 n_given =
  let () = assert (n_given >=0) in
  let rec visit n =
    if n = 0 then 1
    else let ih = visit (pred n)
    	 in ih + n*2+1
  in visit n_given;;

let () = assert (test_oddsum oddsum_v1);;

let oddsum_v2 n_given =
  let () = assert (n_given >=0) in
  parafold_right_nat 1 (fun n' ih -> 2* (succ n') +1 + ih) n_given;;

let () = assert (test_oddsum oddsum_v2);;

let oddsum_v3 n_given =
  let () = assert (n_given >=0) in
  (n_given + 1) * (n_given + 1);;

let () = assert (test_oddsum oddsum_v3);;

(* We can also define oddsum using structural recursion fold_right *) 
let oddsum_v4 n_given =
  let () = assert (n_given >= 0) in
  let (index, oddsum) = fold_right_nat (0,1) (fun (ind, oddsum) -> (ind + 1, oddsum + (ind + 1) * 2 + 1)) n_given
  in oddsum;;

let () = assert (test_oddsum oddsum_v4);;

(* write a fake function that passes the unit test *)
let oddsum_bugged n_given =
  let () = assert (n_given >=0) in
  if n_given <= 20
  then oddsum_v3 n_given
  else 42;;

let () = assert (test_oddsum oddsum_bugged);;  

(* Part g *)
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

let test_fibrule candidate =
  let b0 = (1 + sum_v1 candidate 0 = candidate 2)
  and b1 = (1 + sum_v1 candidate 1 = candidate 3)
  and b2 = (1 + sum_v1 candidate 2 = candidate 4)
  and b3 = (1 + sum_v1 candidate 3 = candidate 5)
  and b4 = (let n = Random.int 20
      	   	in 1 + sum_v1 candidate n = candidate (n+2))
  in b0 && b1 && b2 && b3 && b4;;

let () = assert(test_fibrule fib_v5);;

let test_sum_v1 candidate f =
  let b0 = (candidate f 0 = f 0)
  and b1 = (candidate f 1 = candidate f 0 + f 1)
  and b2 = (candidate f 2 = candidate f 1 + f 2)
  and b3 = (let n = 1 + Random.int 20
      	    in (candidate f n = candidate f (n-1) + f n))
  and b4 = (let n = Random.int 20
            in (candidate f (n+1) = candidate f n + f (n+1)))
  and b5 = (let n = 1 + Random.int 20
      	   	in 1 + candidate fib_v0 n = fib_v0 (n+2))
  in b0 && b1 && b2 && b3 && b4 && b5;;

let () = assert(test_sum_v1 sum_v1 fib_v5);;
let () = assert(test_sum_v1 sum_v2 fib_v5);;
let () = assert(test_sum_v1 sum_bugged fib_v5);;

 
(* ------- Exercise 6 ------ *)

(* Part 1 *)
let test_fold candidate =
  let b0 = (candidate 3 (fun ih -> succ ih) 5 = 8)
  and b1 = (candidate 10 (fun ih -> pred ih) 5 = 5)
  and b2 = (candidate 0 (fun ih -> 9 + ih) 5 = 45)
  and b3 = (candidate 5 (fun ih -> ih) 6 =5)
  in b0 && b1 && b2 && b3;;

let fold_right_nat_bugged zero_case succ_case n_given =
  let () = assert(n_given >= 0) in
  if n_given <= 20
  then fold_right_nat zero_case succ_case n_given
  else 42;;


let () = assert(test_fold fold_right_nat);;
let () = assert(test_fold fold_right_nat_bugged);;

let fold_right_nat_para zero_case succ_case n =
  let ()= assert(n >=0 ) in
 parafold_right_nat zero_case (fun ih ih -> succ_case ih) n;;

let ()= assert(test_fold fold_right_nat_para);;

(* Part 2 *)
let test_para candidate =
  let b0 = (candidate 1 (fun n' ih -> 2* (succ n') +1 + ih) 5 = 36)
  and b1 = (candidate 1 (fun n' ih -> 2* (succ n') +1 + ih) 10 = 121)
  and b2 = (candidate 1 (fun n' ih -> succ n' * ih) 10 = 3628800)
  and b3 = (candidate 1 (fun n' ih -> succ n' * ih) 0 = 1)
  and b4 = (candidate 0 (fun n' ih -> succ n' + ih) 0 = 0)
  and b5 = (candidate 0 (fun n' ih -> succ n' + ih) 5 = 15)
  in b0 && b1 && b2 && b3 && b4 && b5;;

let parafold_right_nat_bugged zero_case succ_case n =
  let () = assert(n >= 0) in
  if n <= 20
  then parafold_right_nat zero_case succ_case n
  else 42;;  

let ()= assert(test_para parafold_right_nat);;
let () = assert(test_para parafold_right_nat_bugged);;

let pair_2 (a,b) = b;;

let parafold_right_nat_fold zero_case succ_case n =
  pair_2 (fold_right_nat (0,zero_case) (fun (n', ih) -> (succ n', succ_case n' ih)) n);;

let () = assert (test_para parafold_right_nat_fold);; 

(* ------- Exercise 9 ------- *)


(* Exercuse 9 *)
let test_ternary ter pre post =
      (* an instance of the base cases: *)
  let b0 = (ter 0 = true)
  and b1 = (pre 0 = false)
  and b2 = (post 0 = false)
      (* an instance of the induction steps: *)
  and b3 = (let n' = Random.int 1000
            in ter(3*n') = pre(3*n'-1))
  and b4 = (let n' = Random.int 1000
            in ter(3*n') = post(3*n'+1))
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4;;


let rec ter n =
  let () = assert (n >= 0) in
  if n = 0
  then true
  else let n' = n - 1
       in pre n'
and pre n =
  if n = 0
  then false
  else let n' = n - 1
       in post n'
and post n =
  if n = 0
  then false
  else let n' = n - 1
       in ter n';;

let () = assert (test_ternary ter pre post);;

let ter_bugged n =
  if n <= 5000
  then ter n
  else false;;

let pre_bugged n =
  if n <= 5000
  then pre n
  else false;;

let post_bugged n =
  if n <= 5000
  then post n
  else false;;

let () = assert (test_ternary ter_bugged pre_bugged post_bugged);;

let test_ternary_v2 ter =
      (* an instance of the base cases: *)
  let b0 = (ter 0 = true)
  and b1 = (ter 1 = false)
  and b2 = (ter 2 = false)
      (* an instance of the induction steps: *)
  and b3 = (let n' = Random.int 1000
            in ter(3*n') = true) 
  and b4 = (let n' = Random.int 1000
            in ter(3*n' + 1) = false)
  and b5 = (let n' = Random.int 1000
             in ter(3*n' + 2) = false)
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5;;


let ter_v1 n_given =
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then (true, false)
    else let n' = n - 1
         in let (ter_n', ter_n) = visit n'
            in (ter_n,  not(ter_n' || ter_n))
  in let (ter_n, ter_succ_n) = visit n_given
     in ter_n;;

let ter_v2 n_given =
      (* base cases: *)
  let () = assert (n_given >= 0) in
  let (ter_n, ter_succ_n) = fold_right_nat (true, false) (fun (ter_n', ter_n) -> (ter_n, not(ter_n' || ter_n))) n_given
in ter_n;;

let () = assert(test_ternary_v2 ter_v1);;

let () = assert(test_ternary_v2 ter_v2);;


let test_mnary m mnary =
      (* an instance of the base cases: *)
  let b0 = (mnary m 0 = true)
  and b1 = (mnary m 1 = false)
  and b2 = (mnary m 2 = false)
      (* an instance of the induction steps: *)
  and b3 = (let n' = Random.int 1000
            in mnary m (m * n') = true)
  and b4 = (let n' = Random.int 1000
            in let r = Random.int m
               in mnary m (m * n' + r) = false)
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4;;

let mnary m n_given =
  let () = assert (n_given >= 0) in
  let rec visit (i, n) =
    if n = 0
    then true
    else begin
      if i = 1 then not(visit (m, pred n))
      else if i = m then not(visit (pred i, pred n))
      else visit (pred i, pred n)
      end
  in visit (m, n_given);;

(* end of liu-recursion.ml *)


