(* term-project_about-three-language-processors-for-arithmetic-expressions.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2019-2020 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Wed 08 Apr 2020, now with error messages in the unit-test functions *)
(* was: *)
(* Version of Sat 04 Apr 2020 *)

(* ********** *)

(* ********** *)

let show_int n =
  if n < 0
  then "~" ^ string_of_int n
  else string_of_int n;;

let show_string s =
 (* show_string : string -> string *)
  "\"" ^ s ^ "\"";;

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

(* ********** *)

(* ********** *)
(* ---------- Adding the functions from mid-term to show evaluation order ---------- *)

let an_int n =
  let () = Printf.printf "processing %s...\n" (show_int n)
  in n;;

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

exception Not_implemented_yet of string;;

(* ********** *)

type arithmetic_expression =
  | Literal of int
  | Plus of arithmetic_expression * arithmetic_expression
  | Minus of arithmetic_expression * arithmetic_expression
  | Quotient of arithmetic_expression * arithmetic_expression
  | Remainder of arithmetic_expression * arithmetic_expression;;

let show_arithmetic_expression ae_given =
  let rec visit ae =
    match ae with
    | Literal n ->
       "Literal " ^ show_int n
    | Plus (ae1, ae2) ->
       "Plus (" ^ visit ae1 ^ ", " ^ visit ae2 ^ ")"
    | Minus (ae1, ae2) ->
       "Minus (" ^ visit ae1 ^ ", " ^ visit ae2 ^ ")"
    | Quotient (ae1, ae2) ->
       "Quotient (" ^ visit ae1 ^ ", " ^ visit ae2 ^ ")"
    | Remainder (ae1, ae2) ->
       "Remainder (" ^ visit ae1 ^ ", " ^ visit ae2 ^ ")"
  in visit ae_given;;

let showp_arithmetic_expression ae =
  "(" ^ show_arithmetic_expression ae ^ ")";;

type source_program =
  | Source_program of arithmetic_expression;;

let show_source_program (Source_program ae) =
  "Source_program " ^ showp_arithmetic_expression ae;;

let showp_source_program sp =
  "(" ^ show_source_program sp ^ ")";;

(* ********** *)

type expressible_value =
  | Expressible_int of int
  | Expressible_msg of string;;

let show_expressible_value ev =
  match ev with
  | Expressible_int n ->
     "Expressible_int " ^ show_int n
  | Expressible_msg s ->
     "Expressible_msg " ^ show_string s;;

let showp_expressible_value ev =
  "(" ^ show_expressible_value ev ^ ")";;

(* ********** *)

let int_test_interpret_one name candidate test expected_result given_source_program =
  let actual_result = candidate given_source_program
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "int_test_interpret failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_expressible_value actual_result)
                     (show_expressible_value expected_result)
          in false;;

let int_test_interpret name candidate_interpret =
 (* int_test_interpret : string -> (source_program -> expressible_value) -> bool *) 
  let b0 = int_test_interpret_one
             name
             candidate_interpret
             "b0"
             (Expressible_int 0)
             (Source_program (Literal 0))
  and b1 = int_test_interpret_one
             name
             candidate_interpret
             "b1"
             (Expressible_int 1)
             (Source_program (Plus (Literal 1, Literal 0)))
  and b2 = int_test_interpret_one
             name
             candidate_interpret
             "b2"
             (Expressible_int 11)
             (Source_program (Plus (Literal 10, Plus (Literal 1, Literal 0))))
  and b3 = int_test_interpret_one
             name
             candidate_interpret
             "b3"
             (Expressible_int 11)
             (Source_program (Plus (Plus (Literal 10, Literal 1), Literal 0)))
  and b4 = int_test_interpret_one
             name
             candidate_interpret
             "b4"
             (Expressible_int 0)
             (Source_program (Minus (Literal 10, Literal 10)))
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4;;

let msg_test_interpret_one name candidate test expected_result given_source_program =
  let actual_result = candidate given_source_program
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "msg_test_interpret failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_expressible_value actual_result)
                     (show_expressible_value expected_result)
          in false;;

let msg_test_interpret name candidate_interpret =
 (* msg_test_interpret : string (source_program -> expressible_value) -> bool *) 
  let b0 = msg_test_interpret_one
             name
             candidate_interpret
             "b0"
             (Expressible_msg "quotient of 0 over 0")
             (Source_program (Quotient (Literal 0, Literal 0)))
  and b1 = msg_test_interpret_one
             name
             candidate_interpret
             "b0"
             (Expressible_msg "remainder of 0 over 0")
             (Source_program (Remainder (Literal 0, Literal 0)))
  (* etc. *)
  in b0 && b1;;

(* ********** *)

(* ---------- Task 1: Implement an interpreter ---------- *)

let interpret (Source_program e) =
 (* interpret : source_program -> expressible_value *)
  let rec evaluate e =
       (* evaluate : arithmetic_expression -> expressible_value *)
    match e with
    | Literal n ->
       Expressible_int n
    | Plus (e1, e2) ->
       (match evaluate e2 with
        | Expressible_int n2 ->
           (match evaluate e1 with
            | Expressible_int n1 ->
               Expressible_int (n1 + n2)
            | Expressible_msg s ->
               Expressible_msg s
           )
        | Expressible_msg s ->
           Expressible_msg s)
    | Minus (e1, e2) ->
       (match evaluate e2 with
        | Expressible_int n2 ->
           (match evaluate e1 with
            | Expressible_int n1 -> Expressible_int (n1 - n2)
            | Expressible_msg s -> Expressible_msg s)
        | Expressible_msg s -> Expressible_msg s)
    | Quotient (e1, e2) ->
       (match evaluate e2 with
        | Expressible_int n2 ->
           (match evaluate e1 with
            | Expressible_int n1 ->
               if n2 = 0 then
                 (Expressible_msg ("quotient of " ^ string_of_int n1 ^ " over 0"))
               else Expressible_int (n1 / n2)
            | Expressible_msg s -> Expressible_msg s)
        | Expressible_msg s -> Expressible_msg s)
    | Remainder (e1, e2) ->
       (match evaluate e2 with
        | Expressible_int n2 ->
           (match evaluate e1 with
            | Expressible_int n1 ->
               if n2 = 0 then
                 (Expressible_msg ("remainder of " ^ string_of_int n1 ^ " over 0"))
               else Expressible_int (n1  mod n2)
            | Expressible_msg s -> Expressible_msg s)
        | Expressible_msg s -> Expressible_msg s)
  in evaluate e;;

let () = assert (int_test_interpret "interpret" interpret);;

let () = assert (msg_test_interpret "interpret" interpret);;


(* ********** *)

type byte_code_instruction =
  | Push of int
  | Add
  | Sub
  | Quo
  | Rem;;

let show_byte_code_instruction bci =
  match bci with
  | Push n ->
     "Push " ^ (show_int n)
  | Add ->
     "Add"
  | Sub ->
     "Sub"
  | Quo ->
     "Quo"
  | Rem ->
     "Rem";;

type target_program =
  | Target_program of byte_code_instruction list;;

let show_target_program (Target_program bcis) =
  "Target_program " ^ (show_list show_byte_code_instruction bcis);;

let showp_target_program tp =
  "(" ^ show_target_program tp ^ ")";;

(* ********** *)

type stackable_value = int;;
  
type data_stack = stackable_value list;;
  
let show_data_stack ds =
  show_list show_int ds;;

type result_of_decoding_and_execution =
  | OK of data_stack
  | KO of string;;

let show_result_of_decoding_and_execution r =
  match r with
  | OK ds ->
     "OK " ^ show_data_stack ds
  | KO s ->
     "KO " ^ show_string s;;

let test_decode_execute_one name candidate test expected_result given_bci given_ds =
  let actual_result = candidate given_bci given_ds
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_decode_execute failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_result_of_decoding_and_execution actual_result)
                     (show_result_of_decoding_and_execution expected_result)
          in false;;

let test_decode_execute name candidate_decode_execute =
 (* test_decode_execute : string -> (byte_code_instruction -> data_stack -> result_of_decoding_and_execution) -> bool *)
  let b0 = test_decode_execute_one
             name
             candidate_decode_execute
             "b0"
             (OK [33])
             (Push 33)
             []
  and b1 = test_decode_execute_one
             name
             candidate_decode_execute
             "b1"
             (OK [33; 34; 35])
             (Push 33)
             [34; 35]
  and b2 = test_decode_execute_one
             name
             candidate_decode_execute
             "b2"
             (KO "stack underflow for Add")
             Add
             []
  and b3 = test_decode_execute_one
             name
             candidate_decode_execute
             "b3"
             (KO "stack underflow for Add")
             Add
             [10]
  and b4 = test_decode_execute_one
             name
             candidate_decode_execute
             "b4"
             (OK [20])
             Add
             [10; 10]
  and b5 = test_decode_execute_one
             name
             candidate_decode_execute
             "b5"
             (KO "quotient of 0 over 0")
             Quo
             [0; 0]

(* we added a few more tests for Sub, Quo, and Rem *)
  and b6 = test_decode_execute_one
             name
             candidate_decode_execute
             "b6"
             (KO "stack underflow for Sub")
             Sub
             []
  and b7 = test_decode_execute_one
             name
             candidate_decode_execute
             "b7"
             (KO "stack underflow for Sub")
             Sub
             [10]
  and b8 = test_decode_execute_one
             name
             candidate_decode_execute
             "b8"
             (OK [~-10])
             Sub
             [10; 20]
  and b9 = test_decode_execute_one
             name
             candidate_decode_execute
             "b9"
             (KO "quotient of 10 over 0")
             Quo
             [10; 0]
  and b10 = test_decode_execute_one
             name
             candidate_decode_execute
             "b10"
             (KO "stack underflow for Quo")
             Quo
             []
  and b11 = test_decode_execute_one
             name
             candidate_decode_execute
             "b11"
             (KO "stack underflow for Quo")
             Quo
             [10]
  and b12 = test_decode_execute_one
             name
             candidate_decode_execute
             "b12"
             (OK [2])
             Quo
             [20; 10]
  and b13 = test_decode_execute_one
             name
             candidate_decode_execute
             "b13"
             (KO "remainder of 10 over 0")
             Rem
             [10; 0]
  and b14 = test_decode_execute_one
             name
             candidate_decode_execute
             "b14"
             (KO "stack underflow for Rem")
             Rem
             []
  and b15 = test_decode_execute_one
             name
             candidate_decode_execute
             "b15"
             (KO "stack underflow for Rem")
             Rem
             [10]
  and b16 = test_decode_execute_one
             name
             candidate_decode_execute
             "b16"
             (OK [2])
             Rem
             [20; 3]

  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8 && b9 && b10 && b11 && b12 && b13 && b14 && b15 && b16;;


(* ---------- Task 2: Implement a byte-code instruction processor ---------- *)
let decode_execute bci ds =
 (* decode_execute : byte_code_instruction -> data_stack -> result_of_execution *)
  match bci with
  | Push n -> OK ( n:: ds)
  | Add -> (match ds with
           |  ( n2 ::  n1 :: ds') -> OK ( (n1+n2) :: ds')
           | _ -> KO "stack underflow for Add")
  | Sub -> (match ds with
           | (n2 :: n1 :: ds') -> OK( (n2 - n1) :: ds')
           | _ -> (KO "stack underflow for Sub"))
  | Quo -> (match ds with
            | ( n2 ::  n1 :: ds') -> if n1 = 0 then KO ( "quotient of " ^ string_of_int n2 ^ " over 0")
                                     else OK( (n2 / n1) :: ds')
            | _ -> (KO "stack underflow for Quo"))
  | Rem -> (match ds with
            | ( n2 ::  n1 :: ds') -> if n1 = 0 then KO ( "remainder of " ^ string_of_int n2 ^ " over 0")
                                     else OK( (n2 mod n1) :: ds')
            | _ -> (KO "stack underflow for Rem"));;


let () = assert (test_decode_execute "decode execute" decode_execute);;
 
(* ********** *)

let int_test_run_one name candidate test expected_result given_target_program =
  let actual_result = candidate given_target_program
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "int_test_run failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_expressible_value actual_result)
                     (show_expressible_value expected_result)
          in false;;

let int_test_run name candidate_run =
 (* int_test_run : string -> (target_program -> expressible_value) -> bool *)
  let b0 = int_test_run_one
             name
             candidate_run
             "b0"
             (Expressible_int 0)
             (Target_program [Push 0])
  and b1 = int_test_run_one
             name
             candidate_run
             "b1"
             (Expressible_int 1)
             (Target_program [Push 1; Push 0; Add])
  and b2 = int_test_run_one
             name
             candidate_run
             "b2"
             (Expressible_int 11)
             (Target_program [Push 10; Push 1; Push 0; Add; Add])
  and b3 = int_test_run_one
             name
             candidate_run
             "b3"
             (Expressible_int 11)
             (Target_program [Push 10; Push 1; Add; Push 0; Add])
  and b4 = int_test_run_one
             name
             candidate_run
             "b4"
             (Expressible_int 0)
             (Target_program [Push 10; Push 10; Sub])
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4;;

let msg_test_run_one name candidate test expected_result given_target_program =
  let actual_result = candidate given_target_program
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "msg_test_run failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_expressible_value actual_result)
                     (show_expressible_value expected_result)
          in false;;

let msg_test_run name candidate_run =
 (* msg_test_run : string -> (target_program -> expressible_value) -> bool *)
  let b0 = msg_test_run_one
             name
             candidate_run
             "b0"
             (Expressible_msg "stack underflow at the end")
             (Target_program [])
  and b1 = msg_test_run_one
             name
             candidate_run
             "b1"
             (Expressible_msg "stack overflow at the end")
             (Target_program [Push 2; Push 3])
  and b2 = msg_test_run_one
             name
             candidate_run
             "b2"
             (Expressible_msg "stack underflow for Add")
             (Target_program [Add])
  and b3 = msg_test_run_one
             name
             candidate_run
             "b3"
             (Expressible_msg "stack underflow for Add")
             (Target_program [Push 2; Add])
  and b4 = msg_test_run_one
             name
             candidate_run
             "b4"
             (Expressible_msg "quotient of 0 over 0")
             (Target_program [Push 0; Push 0; Quo])
  and b5 = msg_test_run_one
             name
             candidate_run
             "b5"
             (Expressible_msg "remainder of 0 over 0")
             (Target_program [Push 0; Push 0; Rem])
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5;;

let run (Target_program bcis) =
 (* run : target_program -> expressible_value *)
  let rec fetch_decode_execute bcis ds =
       (* fetch_decode_execute : byte_code_instruction list -> data_stack -> result_of_execution *)
    match bcis with
    | [] ->
       OK ds
    | bci :: bcis' ->
       (match decode_execute bci ds with
        | OK ds' ->
          fetch_decode_execute bcis' ds'
        | KO s ->
           KO s)
  in match fetch_decode_execute bcis [] with
     | OK [] ->
        Expressible_msg "stack underflow at the end"
     | OK (n :: []) ->
        Expressible_int n
     | OK (n :: _ :: _) ->
        Expressible_msg "stack overflow at the end"
     | KO s ->
        Expressible_msg s;;

let () = assert (int_test_run "run" run);;

let () = assert (msg_test_run "run" run);;
 
(* ***** *)

let traced_run (Target_program bcis) =
 (* run : target_program -> expressible_value *)
  let rec fetch_decode_execute bcis ds =
       (* fetch_decode_execute : byte_code_instruction list -> data_stack -> result_of_execution *)
    Printf.printf "fetch_decode_execute\n  %s\n  %s\n"
                  (show_list show_byte_code_instruction bcis)
                  (show_data_stack ds);
    match bcis with
    | [] ->
       OK ds
    | bci :: bcis' ->
       (match decode_execute bci ds with
        | OK ds' ->
          fetch_decode_execute bcis' ds'
        | KO s ->
           KO s)
  in let result = fetch_decode_execute bcis []
     in Printf.printf "fetch_decode_execute <- %s\n"
                      (show_result_of_decoding_and_execution result);
        match result with
        | OK [] ->
           Expressible_msg "stack underflow at the end"
        | OK (n :: []) ->
           Expressible_int n
        | OK (n :: _ :: _) ->
           Expressible_msg "stack overflow at the end"
        | KO s ->
           Expressible_msg s;;

(* ********** *)

let test_compile_one name candidate_compile test expected_result given_source_program =
  let actual_result = candidate_compile given_source_program
  in if actual_result = expected_result
     then true
     else let () = Printf.printf
                     "test_compile failed for %s in %s with result %s instead of %s\n"
                     name
                     test
                     (show_target_program actual_result)
                     (show_target_program expected_result)
          in false;;

let test_compile name candidate_compile =
 (* test_compile : (source_program -> byte_code_program) -> bool *)
  let b0 = test_compile_one
             name
             candidate_compile
             "b0"
             (Target_program [Push 32])
             (Source_program (Literal 32))
  and b1 = test_compile_one
             name
             candidate_compile
             "b1"
             (Target_program [Push 10; Push 1; Add])
             (Source_program (Plus (Literal 1, Literal 10)))
  and b2 = test_compile_one
             name
             candidate_compile
             "b2"
             (Target_program [Push 2; Push 20; Add; Push 10; Push 1; Add; Add])
             (Source_program (Plus (Plus (Literal 1, Literal 10), Plus (Literal 20, Literal 2))))
  and b3 = test_compile_one
             name
             candidate_compile
             "b3"
             (Target_program [Push 2; Push 20; Add; Push 10; Add; Push 1; Add])
             (Source_program (Plus (Literal 1, Plus (Literal 10, Plus (Literal 20, Literal 2)))))
  and b4 = test_compile_one
             name
             candidate_compile
             "b4"
             (Target_program [Push 2; Push 20; Push 10; Add; Add; Push 1; Add])
             (Source_program (Plus (Literal 1, Plus (Plus (Literal 10, Literal 20), Literal 2))))
  and b5 = test_compile_one
             name
             candidate_compile
             "b5"
             (Target_program [Push 5; Push 4; Quo])
             (Source_program (Quotient (Literal 4, Literal 5)))
  (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5;;

(* ---------- Task 4: Implement a compiler ---------- *)

let compile (Source_program e) =
 (* compile : source_program -> target_program *)
  let rec translate e =
       (* translate : arithmetic_expression -> byte_code_instruction list *)
    match e with
    | Literal n ->
       [Push n]
    | Plus (e1, e2) ->
       List.append (List.append (translate e2)  (translate e1))  [Add]
    | Minus (e1, e2) ->
       List.append (List.append (translate e2)  (translate e1)) [Sub]
    | Quotient (e1, e2) ->
       List.append (List.append (translate e2)  (translate e1)) [Quo]
    | Remainder (e1, e2) ->
       List.append (List.append (translate e2)  (translate e1)) [Rem]
  in Target_program (translate e);;

let () = assert (test_compile "compile" compile);;
(* NOTE: This function compile has also passed the commutativity test implemented below, as we will test later in the code *)

(* ********** *)

let compile_v2 (Source_program e) =
  let rec translate e a =
    match e with
    | Literal n ->
       [Push n] @ a
    | Plus (e1, e2) ->
       (let a = [Add] @ a
        in translate e2 (translate e1 a))
    | Minus (e1, e2) ->
       (let a = [Sub] @ a
        in translate e2 (translate e1 a))
    | Quotient (e1, e2) ->
       (let a = [Quo] @ a
        in translate e2 (translate e1 a))
    | Remainder (e1, e2) ->
       (let a = [Rem] @ a 
        in translate e2 (translate e1 a))
  in Target_program(translate e []);;

(* an observation during debugging: the order of translation matters! i.e. e1 first vs e2 first*)

let () = assert (test_compile "compile_v2" compile_v2);;
(* NOTE: This function compile_v2 has also passed the commutativity test implemented below, as we will test later in the code *)

(* ********** *)

let generate_random_arithmetic_expression n_init =
 (* generate_random_arithmetic_expression : int -> arithmetic_expression *)
  if n_init < 0
  then raise (Failure "generate_random_arithmetic_expression")
  else let rec generate n =
         if n = 0
         then Literal (Random.int 100)
         else match Random.int 5 with
              | 0 ->
                 Literal ~-(Random.int 100)
              | 1 ->
                 Plus (generate (n - 1), generate (n - 1))
              | 2 ->
                 Minus (generate (n - 1), generate (n - 1))
              | 3 ->
                 Quotient (generate (n - 1), generate (n - 1))
              | _ ->
                 Remainder (generate (n - 1), generate (n - 1))
       in generate n_init;;

(* ********** *)

let repeat n_init thunk =
  assert (n_init >= 0);
  let rec loop n =
    if n = 0
    then true
    else thunk () && loop (pred n)
  in loop n_init;;

(* ********** *)

(* ----------- Task 6: unit-test to verify commutativity ----------- *)


let commutativity_test_one candidate_interpret candidate_compile candidate_run p =
  candidate_interpret p = candidate_run (candidate_compile p);;


let commutativity_test candidate_interpret candidate_compile candidate_run =
   (* commutativity_test : (source_program -> expressible_value) ->
                         (source_program -> target_program) ->
                         (target_program -> expressible_value) ->
                         source_program ->
                         bool *)
  let b0 = let thunk = (fun () ->
               let p = Source_program (generate_random_arithmetic_expression 10)
               in commutativity_test_one candidate_interpret candidate_compile candidate_run p)
           in repeat 10 thunk
  in b0;;

let () = assert(commutativity_test interpret compile run);;
let () = assert(commutativity_test interpret compile_v2 run);;

(*
OLD VERSION:
let commutativity_test candidate_interpret candidate_compile candidate_run p =
 (* commutativity_test : (source_program -> expressible_value) ->
                         (source_program -> target_program) ->
                         (target_program -> expressible_value) ->
                         source_program ->
                         bool *)
  candidate_interpret p = candidate_run (candidate_compile p);;

let commutativity_test_one () = 
     let p = (Source_program (generate_random_arithmetic_expression 10)) in
     commutativity_test interpret compile run p;;

let () = assert (repeat 10 commutativity_test_one);;
 *)

(* an experiment 
Unit test functions with printing
let commutativity_test_one_print () =
  let p = (Source_program (generate_random_arithmetic_expression 5)) in
  let () = Printf.printf "%s\n" (show_target_program (compile p)) in
  let () = Printf.printf "%s\n" (show_source_program p) in
  let () = match  (interpret p) with
    | Expressible_int n ->
       Printf.printf "Interpret result %i\n" n
    | Expressible_msg s ->
       Printf.printf "Interpret result %s\n" s
  in let () = match ( run(compile p)) with
       | Expressible_int n ->
          Printf.printf "Run Compile result %i\n" n
       | Expressible_msg s ->
          Printf.printf "Run Compile result %s\n" s
     in commutativity_test interpret compile run p;;

let () =assert (repeat 10 commutativity_test_one_print);;
 *)



(* ----------- Task 7: fold_right version for the interpreter ---------- *)


(* Fold right for arithmetic expression *)
let fold_right_arithmetic literal_case plus_case minus_case quotient_case remainder_case (Source_program e) =
 let rec evaluate e =
    match e with
    | Literal n ->
       literal_case n
    | Plus (e1, e2) ->
       plus_case (evaluate e1) (evaluate e2)
    | Minus (e1, e2) ->
       minus_case (evaluate e1) (evaluate e2)
    | Quotient (e1, e2) ->
       quotient_case (evaluate e1) (evaluate e2)
    | Remainder (e1, e2) ->
       remainder_case (evaluate e1) (evaluate e2)
  in evaluate e;;


let interpret_fold_right (Source_program e) =
  let literal_case n = Expressible_int n
  in let plus_case e1 e2 = 
       match e2 with
       | Expressible_msg s ->
          Expressible_msg s
       | Expressible_int n2 ->
          (match e1 with
           | Expressible_msg s ->
              Expressible_msg s
           | Expressible_int n1 ->
              Expressible_int (n1 + n2))
     in let minus_case e1 e2 = 
       match e2 with
       | Expressible_msg s ->
          Expressible_msg s
       | Expressible_int n2 ->
          (match e1 with
           | Expressible_msg s ->
              Expressible_msg s
           | Expressible_int n1 ->
              Expressible_int (n1 - n2)
          )
        in let quotient_case e1 e2 =
             match e2 with
             | Expressible_msg s ->
                Expressible_msg s
             | Expressible_int n2 ->
                (match e1 with
                 | Expressible_msg s ->
                    Expressible_msg s
                 | Expressible_int n1 ->
                    if n2 = 0 then
                      (Expressible_msg ("quotient of " ^ string_of_int n1 ^ " over 0") )
                    else Expressible_int (n1 / n2)
                )
           in let remainder_case e1 e2 =
                match e2 with
                | Expressible_msg s ->
                   Expressible_msg s
                 | Expressible_int n2 ->
                    (match e1 with
                     | Expressible_msg s ->
                        Expressible_msg s
                    | Expressible_int n1 ->
                       if n2=0 then
                         (Expressible_msg ("remainder of " ^ string_of_int n1 ^ " over 0") )
                       else Expressible_int (n1  mod n2)
                    )
              in fold_right_arithmetic literal_case plus_case minus_case quotient_case remainder_case (Source_program e);;

let () = assert (int_test_interpret "interpret_fold_right" interpret_fold_right);;
let () = assert (msg_test_interpret "interpret_fold_right" interpret_fold_right);;


(* ----------- Task 8: fold_right version for the compiler ---------- *)

let compile_v1_fold_right (Source_program e) =
  (* compile_v2 : source_program -> target_program *)
  let rec translate e =
    let literal_case n = [Push n]
    in let plus_case e1 e2 = List.append (List.append e2 e1)  [Add]
       in let minus_case e1 e2 = List.append (List.append e2 e1)  [Sub]
          in let quotient_case e1 e2 = List.append (List.append e2 e1) [Quo]
             in let remainder_case e1 e2 = List.append (List.append e2 e1)  [Rem]
                in fold_right_arithmetic literal_case plus_case minus_case quotient_case remainder_case (Source_program e)
in Target_program (translate e);;


let () = assert (test_compile "compile_v1_fold_right" compile_v1_fold_right);;

let compile_v2_fold_right (Source_program e) =
  let rec translate e =
    let literal_case n = (fun a -> [Push n] @ a)
    in let plus_case e1 e2 =
         (fun a -> (let a = [Add] @ a
                    in e2 (e1 a)))
       in let minus_case e1 e2 = 
            (fun a -> (let a = [Sub] @ a
                       in e2 (e1 a)))
          in let quotient_case e1 e2 =
               (fun a -> (let a = [Quo] @ a
                          in e2 (e1 a)))
             in let remainder_case e1 e2 =
                  (fun a -> (let a = [Rem] @ a
                             in e2 (e1 a)))
                in fold_right_arithmetic literal_case plus_case minus_case quotient_case remainder_case (Source_program e)[]
  in Target_program (translate e);;

let () = assert (test_compile "compile_v2_fold_right" compile_v2_fold_right);;

(* ********** *)

(* end of term-project_about-three-language-processors-for-arithmetic-expressions.ml *)
