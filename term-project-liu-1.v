(* term-project.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 15 Nov 2020 *)

(* ********** *)

(* Three language processors for arithmetic expressions. *)

(*
   name: Zhang Liu
   student ID number: A0190879J
   e-mail address: zhangliu@u.yale-nus.edu.sg
*)

(* ********** *)

(*

The primary goal of this term project is to prove the following theorem:

  Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret sp = run (compile sp).

for

* a source language of arithmetic expressions:

    Inductive arithmetic_expression : Type :=
    | Literal : nat -> arithmetic_expression
    | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
    | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

    Inductive source_program : Type :=
    | Source_program : arithmetic_expression -> source_program.

* a target language of byte-code instructions:

    Inductive byte_code_instruction : Type :=
    | PUSH : nat -> byte_code_instruction
    | ADD : byte_code_instruction
    | SUB : byte_code_instruction.

    Inductive target_program : Type :=
    | Target_program : list byte_code_instruction -> target_program.

* a semantics of expressible values:

    Inductive expressible_value : Type :=
    | Expressible_nat : nat -> expressible_value
    | Expressible_msg : string -> expressible_value.

* a source interpreter

    interpret : source_program -> expressible_value

* a compiler

    compile : source_program -> target_program

* a target interpreter

    run : target_program -> expressible_value

The source for errors is subtraction,
since subtracting two natural numbers does not always yield a natural number:
for example, 3 - 2 is defined but not 2 - 3.

You are expected, at the very least:

* to implement a source interpreter
  and to verify that it satisfies its specification

* to implement a target interpreter (i.e., a virtual machine)
  and to verify that it satisfies its specification

* to implement a compiler
  and to verify that it satisfies its specification

* to prove that the diagram commutes, i.e., to show that
  interpreting any given expression
  gives the same result as
  compiling this expression and then running the resulting compiled program

Beyond this absolute minimum, in decreasing importance, it would be good:

* to make a copy of the above in a separate file
  and modify it mutatis mutandis
  so that the three language processors operate from right to left instead of from left to right,

* to write an accumulator-based compiler and to prove that it satisfies the specification,

* to investigate byte-code verification,

* to investigate decompilation, and

* if there is any time left, to prove that each of the specifications specifies a unique function.

Also, feel free to expand the source language and the target language,
e.g., with multiplication, quotient, and modulo.

*)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

(* caution: only use natural numbers up to 5000 *)
Definition string_of_nat (q0 : nat) : string :=
  let s0 := String (ascii_of_nat (48 + (q0 mod 10))) EmptyString
  in if q0 <? 10
     then s0
     else let q1 := q0 / 10
          in let s1 := String (ascii_of_nat (48 + (q1 mod 10))) s0
             in if q1 <? 10
                then s1
                else let q2 := q1 / 10
                     in let s2 := String (ascii_of_nat (48 + (q2 mod 10))) s1
                        in if q2 <? 10
                           then s2
                           else let q3 := q2 / 10
                                in let s2 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                        in if q3 <? 10
                           then s2
                           else "00000".

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
| Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
| Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
| Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     evaluate (Literal n) = Expressible_nat n)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2))).

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Task 1:
   a. time permitting, prove that each of the definitions above specifies at most one function;
   b. implement these two functions; and
   c. verify that each of your functions satisfies its specification.
 *)

(* Task 1a: evaluate *)

Theorem there_is_at_most_one_evaluate_function :
  forall evaulate_1 evaulate_2 : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaulate_1 ->
    specification_of_evaluate evaulate_2 ->
    forall ae : arithmetic_expression,
      evaulate_1 ae = evaulate_2 ae.
Proof.
  (* a proof where *all* the components of
     the specification are not named at the outset,
     but only the relevant component of
     the specification in each case *)

  intros evaluate_1 evaluate_2 S_evaluate_1 S_evaluate_2 ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]. 
  - unfold specification_of_evaluate in S_evaluate_1.
    destruct S_evaluate_1 as [H_Literal_1 _].
    destruct S_evaluate_2 as [H_Literal_2 _].
    rewrite -> (H_Literal_1 n).
    rewrite -> (H_Literal_2 n).
    reflexivity.
  - case (evaluate_2 ae1) as [n1 | s1] eqn:IHae1'.
    + case (evaluate_2 ae2) as [n2 | s2] eqn:IHae2'.
      * destruct S_evaluate_1 as [_ [[_ [_ H_Plus_1]] _]].
        destruct S_evaluate_2 as [_ [[_ [_ H_Plus_2]] _]].
        Check (H_Plus_2 ae1 ae2 n1 n2 IHae1' IHae2').
        rewrite -> (H_Plus_2 ae1 ae2 n1 n2 IHae1' IHae2').
        Check (H_Plus_1 ae1 ae2 n1 n2 IHae1 IHae2).
        exact (H_Plus_1 ae1 ae2 n1 n2 IHae1 IHae2).
      * destruct S_evaluate_1 as [_ [[_ [H_Plus_1_error2 _]] _]].
        destruct S_evaluate_2 as [_ [[_ [H_Plus_2_error2 _]] _]].
        Check (H_Plus_2_error2 ae1 ae2 n1 s2 IHae1' IHae2').
        rewrite -> (H_Plus_2_error2 ae1 ae2 n1 s2 IHae1' IHae2').
        Check (H_Plus_1_error2 ae1 ae2 n1 s2 IHae1 IHae2).
        exact (H_Plus_1_error2 ae1 ae2 n1 s2 IHae1 IHae2).
    + destruct S_evaluate_1 as [_ [[H_Plus_1_error1 _] _]].
      destruct S_evaluate_2 as [_ [[H_Plus_2_error1 _] _]].
      Check (H_Plus_2_error1 ae1 ae2 s1 IHae1').
      rewrite -> (H_Plus_2_error1 ae1 ae2 s1 IHae1').
      Check (H_Plus_1_error1 ae1 ae2 s1 IHae1).
      exact (H_Plus_1_error1 ae1 ae2 s1 IHae1).
  - case (evaluate_2 ae1) as [n1 | s1] eqn:IHae1'.
    + case (evaluate_2 ae2) as [n2 | s2] eqn:IHae2'. 
      ++ case (n1 <? n2) eqn:H_underflow.
         ** destruct S_evaluate_1 as [_ [_ [_ [_ [H_Minus_1_underflow _]]]]].
            destruct S_evaluate_2 as [_ [_ [_ [_ [H_Minus_2_underflow _]]]]].
            Check (H_Minus_2_underflow ae1 ae2 n1 n2 IHae1' IHae2' H_underflow).
            rewrite -> (H_Minus_2_underflow ae1 ae2 n1 n2 IHae1' IHae2' H_underflow).
            Check (H_Minus_1_underflow ae1 ae2 n1 n2 IHae1 IHae2 H_underflow).
            exact (H_Minus_1_underflow ae1 ae2 n1 n2 IHae1 IHae2 H_underflow).
         ** destruct S_evaluate_1 as [_ [_ [_ [_ [_ H_Minus_1]]]]].
            destruct S_evaluate_2 as [_ [_ [_ [_ [_ H_Minus_2]]]]].
            Check (H_Minus_2 ae1 ae2 n1 n2 IHae1' IHae2' H_underflow).
            rewrite -> (H_Minus_2 ae1 ae2 n1 n2 IHae1' IHae2' H_underflow).
            Check (H_Minus_1 ae1 ae2 n1 n2 IHae1 IHae2 H_underflow).
            exact (H_Minus_1 ae1 ae2 n1 n2 IHae1 IHae2 H_underflow).
      ++ destruct S_evaluate_1 as [_ [_ [_ [H_Minus_1_error2 _]]]].
         destruct S_evaluate_2 as [_ [_ [_ [H_Minus_2_error2 _]]]].
         Check (H_Minus_2_error2 ae1 ae2 n1 s2 IHae1' IHae2').
         rewrite -> (H_Minus_2_error2 ae1 ae2 n1 s2 IHae1' IHae2').
         Check (H_Minus_1_error2 ae1 ae2 n1 s2 IHae1 IHae2).
         exact (H_Minus_1_error2 ae1 ae2 n1 s2 IHae1 IHae2).
    + destruct S_evaluate_1 as [_ [_ [H_Minus_1_error1 _]]].
      destruct S_evaluate_2 as [_ [_ [H_Minus_2_error1 _]]].
      Check (H_Minus_2_error1 ae1 ae2 s1 IHae1').
      rewrite -> (H_Minus_2_error1 ae1 ae2 s1 IHae1').
      Check (H_Minus_1_error1 ae1 ae2 s1 IHae1).
      exact (H_Minus_1_error1 ae1 ae2 s1 IHae1).
Qed.


(* Task 1b : evaluate *)

Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
 match ae with
  | Literal n =>
    Expressible_nat n
  | Plus ae1 ae2 =>
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s =>
        Expressible_msg s
      end
    | Expressible_msg s =>
      Expressible_msg s
    end
  | Minus ae1 ae2 =>
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg
               (String.append
                  "numerical underflow: -"
                  (string_of_nat (n2 - n1)))
        else Expressible_nat (n1 - n2)
      | Expressible_msg s =>
        Expressible_msg s
      end
    | Expressible_msg s =>
      Expressible_msg s
    end
 end.

Lemma fold_unfold_evaluate_Literal :
  forall n : nat,
    evaluate (Literal n) = Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Plus ae1 ae2) =
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s =>
        Expressible_msg s
      end
    | Expressible_msg s =>
      Expressible_msg s
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Minus ae1 ae2) =
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg
               (String.append
                  "numerical underflow: -"
                  (string_of_nat (n2 - n1)))
        else Expressible_nat (n1 - n2)
      | Expressible_msg s =>
        Expressible_msg s
      end
    | Expressible_msg s =>
      Expressible_msg s
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

(* Task 1c: evaluate *)

Theorem evaluate_satisfies_the_specification_of_evaluate :
  specification_of_evaluate evaluate.
Proof.
  unfold specification_of_evaluate. 
  split. 
  - intro n. 
    exact (fold_unfold_evaluate_Literal n).
  - split.
    * split.
      ** intros ae1 ae2 s H_ae1_error.
         rewrite -> fold_unfold_evaluate_Plus.
         rewrite -> H_ae1_error.
         reflexivity.
      ** split.
         *** intros ae1 ae2 n1 s2 H_ae1_nat H_ae2_error.
             rewrite -> fold_unfold_evaluate_Plus.
             rewrite -> H_ae2_error.
             rewrite -> H_ae1_nat.
             reflexivity.
         *** intros ae1 ae2 n1 n2 H_ae1_nat H_ae2_nat.
             rewrite -> fold_unfold_evaluate_Plus.
             rewrite -> H_ae2_nat.
             rewrite -> H_ae1_nat.
             reflexivity.
    * split.
      ** intros ae1 ae2 s H_ae1_error.
         rewrite -> fold_unfold_evaluate_Minus.
         rewrite -> H_ae1_error.
         reflexivity.
      ** split.
         *** intros ae1 ae2 n1 s2 H_ae1_nat H_ae2_error.
             rewrite -> fold_unfold_evaluate_Minus.
             rewrite -> H_ae2_error.
             rewrite -> H_ae1_nat.
             reflexivity.
         *** split.
    + intros ae1 ae2 n1 n2 H_ae1_nat H_ae2_nat H_underflow_error.
      rewrite -> fold_unfold_evaluate_Minus.
      rewrite -> H_ae2_nat.
      rewrite -> H_ae1_nat.
      rewrite -> H_underflow_error.
      reflexivity.
    + intros ae1 ae2 n1 n2 H_ae1_nat H_ae2_nat H_underflow_noerror.
      rewrite -> fold_unfold_evaluate_Minus.
      rewrite -> H_ae2_nat.
      rewrite -> H_ae1_nat.
      rewrite -> H_underflow_noerror.
      reflexivity.
Qed.

(* Task 1a: interpret *)

Theorem there_is_at_most_one_interpret_function :
  forall interpret_1 interpret_2 : source_program -> expressible_value,
    specification_of_interpret interpret_1 ->
    specification_of_interpret interpret_2 ->
    forall ae : arithmetic_expression,
      interpret_1 (Source_program ae) = interpret_2 (Source_program ae).
Proof.
  intros interpret_1 interpret_2.
  unfold specification_of_interpret.
  intros H_interpret_1 H_interpret_2.
  intro ae.
  Check (H_interpret_2 evaluate evaluate_satisfies_the_specification_of_evaluate ae).
  rewrite -> (H_interpret_2 evaluate evaluate_satisfies_the_specification_of_evaluate ae).
  Check (H_interpret_1 evaluate evaluate_satisfies_the_specification_of_evaluate ae).
  exact (H_interpret_1 evaluate evaluate_satisfies_the_specification_of_evaluate ae).
Qed.

(* Task 1b: interpret *)

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae =>
    evaluate ae
  end.

(* Task 1c: interpret *)

Theorem interpret_satisfies_the_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret, interpret.
  intros evaluate' S_evaluate' ae.
  Check (there_is_at_most_one_evaluate_function evaluate evaluate' evaluate_satisfies_the_specification_of_evaluate S_evaluate' ae).
  exact (there_is_at_most_one_evaluate_function evaluate evaluate' evaluate_satisfies_the_specification_of_evaluate S_evaluate' ae).
Qed.

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
| PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

(* Target programs: *)

Inductive target_program : Type :=
| Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (forall (n : nat)
          (ds : data_stack),
     decode_execute (PUSH n) ds = OK (n :: ds))
  /\
  ((decode_execute ADD nil = KO "ADD: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute ADD (n2 :: nil) = KO "ADD: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       decode_execute ADD (n2 :: n1 :: ds) = OK ((n1 + n2) :: ds)))
  /\
  ((decode_execute SUB nil = KO "SUB: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute SUB (n2 :: nil) = KO "SUB: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = true ->
       decode_execute SUB (n2 :: n1 :: ds) = KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = false ->
       decode_execute SUB (n2 :: n1 :: ds) = OK ((n1 - n2) :: ds))).

(* Task 2:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)

(* Task 2a *)

Theorem there_is_at_most_one_decode_execute_function :
  forall dec_exec_1 dec_exec_2 : byte_code_instruction
                                 -> data_stack
                                 -> result_of_decoding_and_execution,
    specification_of_decode_execute dec_exec_1 ->
    specification_of_decode_execute dec_exec_2 ->
    forall (bci : byte_code_instruction)
           (ds : data_stack),
      dec_exec_1 bci ds = dec_exec_2 bci ds.
Proof. 
  intros dec_exec_1 dec_exec_2.
  unfold specification_of_decode_execute.
  intros H_dec_exec_1 H_dec_exec_2.
  destruct H_dec_exec_1 as [H_1_Push
                              [[H_1_ADD_underflow0 [H_1_ADD_underflow1 H_1_ADD]]
                                 [H_1_SUB_underflow0 [H_1_SUB_underflow1 [H_1_SUB_underflow H_1_SUB]]]]].
  destruct H_dec_exec_2 as [H_2_Push
                              [[H_2_ADD_underflow0 [H_2_ADD_underflow1 H_2_ADD]]
                                 [H_2_SUB_underflow0 [H_2_SUB_underflow1 [H_2_SUB_underflow H_2_SUB]]]]].
  intros bci ds.
  induction bci as [ n | | ]. 
  - rewrite -> H_1_Push.
    rewrite -> H_2_Push.
    reflexivity.
  - case ds as [ | n2].
    + rewrite -> H_1_ADD_underflow0.
      rewrite -> H_2_ADD_underflow0.
      reflexivity.  
    + case ds as [ | n1].
      * rewrite -> H_1_ADD_underflow1.
        rewrite -> H_2_ADD_underflow1.
        reflexivity.
      * rewrite -> H_1_ADD.
        rewrite -> H_2_ADD.
        reflexivity.
  - case ds as [ | n2].
    + rewrite -> H_1_SUB_underflow0.
      rewrite -> H_2_SUB_underflow0.
      reflexivity.
    + case ds as [ | n1].
      * rewrite -> H_1_SUB_underflow1.
        rewrite -> H_2_SUB_underflow1.
        reflexivity.
      * case (n1 <? n2) eqn:H_underflow.
        ** rewrite -> (H_1_SUB_underflow n1 n2 ds H_underflow).
           rewrite -> (H_2_SUB_underflow n1 n2 ds H_underflow).
           reflexivity.
        ** rewrite -> (H_1_SUB n1 n2 ds H_underflow).
           rewrite -> (H_2_SUB n1 n2 ds H_underflow).
           reflexivity.

  Restart.

  (* a new proof where *all* the components of
     the specification are not named at the outset,
     but only the relevant component of
     the specification in each case *)

  intros dec_exec_1 dec_exec_2 H_dec_exec_1 H_dec_exec_2.
  induction bci as [ n | | ].
  intro ds.
  - unfold specification_of_decode_execute in H_dec_exec_1.
    destruct H_dec_exec_1 as [H_1_Push _].
    destruct H_dec_exec_2 as [H_2_Push _].
    rewrite -> H_1_Push.
    rewrite -> H_2_Push.
    reflexivity.
  - case ds as [ | n2].
    + destruct H_dec_exec_1 as [_ [[H_1_ADD_underflow0 _] _]].
      destruct H_dec_exec_2 as [_ [[H_2_ADD_underflow0 _] _]].
      rewrite -> H_1_ADD_underflow0.
      rewrite -> H_2_ADD_underflow0.
      reflexivity.
    + case ds as [ | n1].
      * destruct H_dec_exec_1 as [_ [[_ [H_1_ADD_underflow1 _]] _]].
        destruct H_dec_exec_2 as [_ [[_ [H_2_ADD_underflow1 _]] _]].
        rewrite -> H_1_ADD_underflow1.
        rewrite -> H_2_ADD_underflow1.
        reflexivity.
      * destruct H_dec_exec_1 as [_ [[_ [_ H_1_ADD]] _]].
        destruct H_dec_exec_2 as [_ [[_ [_ H_2_ADD]] _]].
        rewrite -> H_1_ADD.
        rewrite -> H_2_ADD.
        reflexivity.
  - case ds as [ | n2].
    + destruct H_dec_exec_1 as [_ [_ [H_1_SUB_underflow0 _]]].
      destruct H_dec_exec_2 as [_ [_ [H_2_SUB_underflow0 _]]].
      rewrite -> H_1_SUB_underflow0.
      rewrite -> H_2_SUB_underflow0.
      reflexivity.
    + case ds as [ | n1].
      * destruct H_dec_exec_1 as [_ [_ [_ [H_1_SUB_underflow1 _]]]].
        destruct H_dec_exec_2 as [_ [_ [_ [H_2_SUB_underflow1 _]]]].
        rewrite -> H_1_SUB_underflow1.
        rewrite -> H_2_SUB_underflow1.
        reflexivity.
      * case (n1 <? n2) eqn:H_underflow.
        ** destruct H_dec_exec_1 as [_ [_ [_ [_ [H_1_SUB_underflow _]]]]].
           destruct H_dec_exec_2 as [_ [_ [_ [_ [H_2_SUB_underflow _]]]]].
           rewrite -> (H_1_SUB_underflow n1 n2 ds H_underflow).
           rewrite -> (H_2_SUB_underflow n1 n2 ds H_underflow).
           reflexivity.
        ** destruct H_dec_exec_1 as [_ [_ [_ [_ [_ H_1_SUB]]]]].
           destruct H_dec_exec_2 as [_ [_ [_ [_ [_ H_2_SUB]]]]].
           rewrite -> (H_1_SUB n1 n2 ds H_underflow).
           rewrite -> (H_2_SUB n1 n2 ds H_underflow).
           reflexivity.
Qed.

(* Task 2b *)

Definition decode_execute (bcis : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | PUSH n =>
    OK (n :: ds)
  | ADD =>
    match ds with
    | nil =>
      KO "ADD: stack underflow"
    | n2 :: nil =>
      KO "ADD: stack underflow"
    | n2 :: n1 :: ds =>
      OK ((n1 + n2) :: ds)
    end
  | SUB =>
    match ds with
    | nil =>
      KO "SUB: stack underflow"
    | n2 :: nil =>
      KO "SUB: stack underflow"
    | n2 :: n1 :: ds =>
      if n1 <? n2
      then KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
      else OK ((n1 - n2) :: ds)
    end
  end.

(* Task 2c *)

Theorem decode_execute_satisfies_the_specification_of_decode_execute :
  specification_of_decode_execute decode_execute.
Proof.
  unfold specification_of_decode_execute, decode_execute.
  split.
  - intros n ds.
    reflexivity.
  - split.
    * split.
      + reflexivity.
      + split.
        intro n.
        reflexivity.

        intros n1 n2 ds.
        reflexivity.

    * split.
      + reflexivity.
      + split.
        intro n.
        reflexivity.

        split.
        intros n1 n2 ds H_underflow.
        rewrite -> H_underflow.
        reflexivity.

        intros n1 n2 ds H_no_underflow.
        rewrite -> H_no_underflow.
        reflexivity.

  Restart.

  unfold specification_of_decode_execute, decode_execute.
  split; [intros n ds | split; [split; [ | split; [intro n | intros n1 n2 ds]] | split; [ | split; [intro n | split; intros n1 n2 ds H_underflow; rewrite -> H_underflow]]]]; reflexivity.
Qed.

(* ********** *)

(* Specification of the virtual machine : *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  forall decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute decode_execute ->
    (forall ds : data_stack,
        fetch_decode_execute_loop nil ds = OK ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack),
        decode_execute bci ds = OK ds' ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        fetch_decode_execute_loop bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack)
            (s : string),
        decode_execute bci ds = KO s ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        KO s).

(* Task 3:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

(* Task 3a *)

Theorem there_is_at_most_one_fetch_decode_execute_loop_function :
  forall fdel_1 fdel_2 : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fdel_1 ->
    specification_of_fetch_decode_execute_loop fdel_2 ->
    forall (bcis : list byte_code_instruction) (ds : data_stack),
      fdel_1 bcis ds = fdel_2 bcis ds.
Proof.
  intros fdel_1 fdel_2.
  unfold specification_of_fetch_decode_execute_loop.
  intros H_fdel_1 H_fdel_2.
  Check (H_fdel_1 decode_execute decode_execute_satisfies_the_specification_of_decode_execute).
  destruct (H_fdel_1 decode_execute decode_execute_satisfies_the_specification_of_decode_execute) as [H_fdel_1_nil [H_fdel_1_cons H_fdel_1_error]].
  Check (H_fdel_2 decode_execute decode_execute_satisfies_the_specification_of_decode_execute).
  destruct (H_fdel_2 decode_execute decode_execute_satisfies_the_specification_of_decode_execute) as [H_fdel_2_nil [H_fdel_2_cons H_fdel_2_error]].
  intros bcis.
  induction bcis as [ | bci' bcis' IHbcis']; intro ds. 
  - rewrite -> (H_fdel_1_nil ds).
    rewrite -> (H_fdel_2_nil ds).
    reflexivity.
  - case (decode_execute bci' ds) as [ds' | s'] eqn:H_bcis_con.
    + Check (H_fdel_1_cons bci' bcis' ds ds' H_bcis_con).
      rewrite -> (H_fdel_1_cons bci' bcis' ds ds' H_bcis_con).
      rewrite -> (H_fdel_2_cons bci' bcis' ds ds' H_bcis_con).
      exact (IHbcis' ds').
    + rewrite -> (H_fdel_1_error bci' bcis' ds s' H_bcis_con).
      rewrite -> (H_fdel_2_error bci' bcis' ds s' H_bcis_con).
      reflexivity.
Qed.

(* Task 3b : Define fetch_decode_execute_loop *)

Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | nil => OK ds
  | bci :: bcis' =>
    match (decode_execute bci ds) with
    | OK ds' => fetch_decode_execute_loop bcis' ds'
    | KO s => KO s
    end
  end.

Lemma fold_unfold_fetch_decode_execute_loop_nil :
  forall ds : data_stack,
    fetch_decode_execute_loop nil ds = OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_cons :
  forall (bci: byte_code_instruction)
         (bcis': list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop (bci :: bcis') ds =
    match decode_execute bci ds with
    | OK ds' => fetch_decode_execute_loop bcis' ds'
    | KO s => KO s
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

(* Task 3c *)

Theorem fetch_decode_execute_loop_satisfies_the_specification :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros decode_execute' H_decode_execute. 
  split. 
  - intro ds.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_nil ds).
    reflexivity.
  - split.
    + intros bci bcis' ds ds'.
      intro H_OK.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci bcis' ds).
      Check there_is_at_most_one_decode_execute_function.
      rewrite -> (there_is_at_most_one_decode_execute_function decode_execute' decode_execute H_decode_execute decode_execute_satisfies_the_specification_of_decode_execute bci ds) in H_OK.
      rewrite -> H_OK.
      reflexivity.
    + intros bci bcis' ds s.
      intro H_KO.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci bcis' ds).
      rewrite -> (there_is_at_most_one_decode_execute_function decode_execute' decode_execute H_decode_execute decode_execute_satisfies_the_specification_of_decode_execute bci ds) in H_KO.
      rewrite -> H_KO.
      reflexivity.
Qed.

(* ********** *)

(* Task 4:
   Prove that for any lists of byte-code instructions bcis1 and bcis2,
   and for any data stack ds,
   executing the concatenation of bcis1 and bcis2 (i.e., bcis1 ++ bcis2) with ds
   gives the same result as
   (1) executing bcis1 with ds, and then
   (2) executing bcis2 with the resulting data stack, if there exists one.
*)

Lemma fold_unfold_append_nil :
  forall bcis2 : list byte_code_instruction,
    nil ++ bcis2 = bcis2.
Proof.
  fold_unfold_tactic List.app.
Qed.

Lemma fold_unfold_append_cons :
  forall (bci1 : byte_code_instruction)
         (bci1s bci2s : list byte_code_instruction),
    (bci1 :: bci1s) ++ bci2s =
    bci1 :: (bci1s ++ bci2s).
Proof.
  fold_unfold_tactic List.app.
Qed.

Theorem concatenation :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds: data_stack) ,
  (forall (ds': data_stack),
    (fetch_decode_execute_loop bcis1 ds) = OK ds'
    ->
    (fetch_decode_execute_loop bcis2 ds') = (fetch_decode_execute_loop (bcis1 ++ bcis2) ds))
  /\
  (forall (s' : string),
      (fetch_decode_execute_loop bcis1 ds) = KO s'
      ->
      KO s' = (fetch_decode_execute_loop (bcis1 ++ bcis2) ds)).
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intro bcis1.
  induction bcis1 as [ | bci bcis1' IHbcis1 ]. 
  + intros bcis2 ds.
    split. 
  -  intros ds' H_OK_nil. 
    rewrite -> (fold_unfold_fetch_decode_execute_loop_nil) in H_OK_nil.
    rewrite -> (fold_unfold_append_nil bcis2).
    injection H_OK_nil. 
    intro H_equal.
    rewrite -> (H_equal).
    reflexivity.  
  - intros s' H_KO_nil.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_nil) in H_KO_nil. 
    discriminate H_KO_nil.
  + intros bcis2 ds.
    split. 
    - intros ds' H_OK_cons.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_cons) in H_OK_cons.
      Check (fold_unfold_append_cons).
      rewrite -> (fold_unfold_append_cons bci bcis1' bcis2).
      Check (fold_unfold_fetch_decode_execute_loop_cons).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci (bcis1' ++ bcis2) ds).
      destruct (decode_execute bci ds) as [ds'' | s']. 
      -- destruct (IHbcis1 bcis2 ds'') as [IHds _]. 
         rewrite -> (IHds ds' H_OK_cons). 
         reflexivity.
      -- discriminate.
    - intros s' H_KO_cons.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_cons) in H_KO_cons.
      Check (fold_unfold_append_cons).
      rewrite -> (fold_unfold_append_cons bci bcis1' bcis2).
      Check (fold_unfold_fetch_decode_execute_loop_cons).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci (bcis1' ++ bcis2) ds).
      destruct (decode_execute bci ds) as [ds'' | s''].
      -- destruct (IHbcis1 bcis2 ds'') as [_ IHs].
         rewrite -> (IHs s' H_KO_cons).
         reflexivity.
      -- symmetry.
         exact H_KO_cons.
Qed.


(* ********** *)

(* Specification of run: *)

Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
       fetch_decode_execute_loop bcis nil = OK nil ->
       run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
       run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
       run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = KO s ->
       run (Target_program bcis) = Expressible_msg s).


(* Task 5:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

(* Task 5a *)

Theorem there_is_at_most_one_run_function :
  forall run1 run2 : target_program -> expressible_value,
    specification_of_run run1 ->
    specification_of_run run2 ->
    forall bcis : list byte_code_instruction,
      run1 (Target_program bcis) = run2 (Target_program bcis).
Proof.
  intros run1 run2.
  unfold specification_of_run.
  intros H_run1 H_run2.
  Check (H_run1 fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification).
  destruct (H_run1 fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification) as [H_run1_nil [H_run1_1 [H_run1_2 H_run1_error]]].
  destruct (H_run2 fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_the_specification) as [H_run2_nil [H_run2_1 [H_run2_2 H_run2_error]]].
  intro bcis.
  case (fetch_decode_execute_loop bcis nil) as [[ | n [ | n' ds'' ]] | s] eqn:H_bcis. 
  - Check (H_run1_nil bcis H_bcis).  
    rewrite -> (H_run1_nil bcis H_bcis).
    rewrite -> (H_run2_nil bcis H_bcis).
    reflexivity.
  - Check (H_run1_1 bcis n H_bcis).
    rewrite -> (H_run1_1 bcis n H_bcis).
    rewrite -> (H_run2_1 bcis n H_bcis).
    reflexivity.
  - Check (H_run1_2 bcis n n' ds'' H_bcis).
    rewrite -> (H_run1_2 bcis n n' ds'' H_bcis).
    rewrite -> (H_run2_2 bcis n n' ds'' H_bcis).
    reflexivity.
  - Check (H_run1_error bcis s H_bcis).
    rewrite -> (H_run1_error bcis s H_bcis).
    rewrite -> (H_run2_error bcis s H_bcis).
    reflexivity.
Qed.

(* Task 5b *)

Definition run (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
    match (fetch_decode_execute_loop bcis nil) with
    | OK nil =>
      Expressible_msg "no result on the data stack"
    | OK (n :: nil) =>
      Expressible_nat n
    | OK (n :: n' :: ds'') =>
      Expressible_msg "too many results on the data stack"
    | KO s =>
      Expressible_msg s
    end
  end.

(* Task 5c *)

Theorem run_satisfies_the_specification_of_run :
  specification_of_run run.
Proof.
  unfold specification_of_run, run.
  intros fedl H_fedl.
  split.    
  - intros bcis H_bcis_nil.
    Check (there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fedl fetch_decode_execute_loop_satisfies_the_specification H_fedl bcis nil).
    rewrite <- (there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fedl fetch_decode_execute_loop_satisfies_the_specification H_fedl bcis nil) in H_bcis_nil.
    rewrite -> H_bcis_nil.
    reflexivity.
  - split.
    + intros bcis n H_bcis_1.
      Check (there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fedl fetch_decode_execute_loop_satisfies_the_specification H_fedl bcis nil).
      rewrite <- (there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fedl fetch_decode_execute_loop_satisfies_the_specification H_fedl bcis nil) in H_bcis_1.
      rewrite -> H_bcis_1.
      reflexivity.
    + split.
      * intros bcis n n' ds'' H_bcis_2.
         Check (there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fedl fetch_decode_execute_loop_satisfies_the_specification H_fedl bcis nil).
         rewrite <- (there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fedl fetch_decode_execute_loop_satisfies_the_specification H_fedl bcis nil) in H_bcis_2.
         rewrite -> H_bcis_2.
         reflexivity. 
      * intros bcis s H_error.
         Check (there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fedl fetch_decode_execute_loop_satisfies_the_specification H_fedl bcis nil).
         rewrite <- (there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fedl fetch_decode_execute_loop_satisfies_the_specification H_fedl bcis nil) in H_error.
         rewrite -> H_error.
         reflexivity.
Qed.

(* ********** *)

(* Specification of compile_aux: *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
      compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).


(* Task 6:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function using list concatenation, i.e., ++; and
   c. verify that your function satisfies the specification.
 *)

(* Task 6a *)

Theorem there_is_at_most_one_compile_aux :
  forall (compile_aux_1 compile_aux_2 : arithmetic_expression -> list byte_code_instruction),
    specification_of_compile_aux compile_aux_1 ->
    specification_of_compile_aux compile_aux_2 ->
    forall (ae : arithmetic_expression),
      compile_aux_1 ae = compile_aux_2 ae.
Proof. 
  intros compile_aux_1 compile_aux_2.
  intros H1 H2 ae.
  destruct H1 as [H_lit_1 [H_plus_1 H_minus_1]].
  destruct H2 as [H_lit_2 [H_plus_2 H_minus_2]].
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]. 
  - rewrite (H_lit_1 n).
    rewrite (H_lit_2 n).
    reflexivity.
  - rewrite (H_plus_1 ae1 ae2).
    rewrite (H_plus_2 ae1 ae2).
    rewrite IHae1.
    rewrite IHae2.
    reflexivity.
  - rewrite (H_minus_1 ae1 ae2).
    rewrite (H_minus_2 ae1 ae2).
    rewrite IHae1.
    rewrite IHae2.
    reflexivity.
Qed.

(* Task 6b *)

Fixpoint compile_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n => PUSH n :: nil
  | Plus ae1 ae2 => (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 => (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)
  end.

Lemma fold_unfold_compile_aux_lit :
  forall n : nat,
    compile_aux (Literal n) = PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_plus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_minus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

(* Task 6c *)

Theorem compile_aux_satisfies_the_specification :
  specification_of_compile_aux compile_aux.
Proof.
  (*
     a simpler proof that doesn't use the intro tactic
     (and makes the relation between fold-unfold lemmas and the components of the specification more patent)
   *)

  unfold specification_of_compile_aux. 
  split.
  - exact fold_unfold_compile_aux_lit.
  - split.
    + exact fold_unfold_compile_aux_plus.
    + exact fold_unfold_compile_aux_minus.
Qed.

(* ********** *)

(* Specification of compile: *)

Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

(* Task 7:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

(* Task 7a *)

Theorem there_is_at_most_one_compile_function :
  forall compile1 compile2 : source_program -> target_program,
    specification_of_compile compile1 ->
    specification_of_compile compile2 ->
    forall ae : arithmetic_expression,
      compile1 (Source_program ae) = compile2 (Source_program ae).
Proof.
  intros compile1 compile2.
  unfold specification_of_compile.
  intros H_compile1 H_compile2 ae.
  rewrite -> ( H_compile1 compile_aux compile_aux_satisfies_the_specification ae).
  rewrite -> (H_compile2 compile_aux compile_aux_satisfies_the_specification ae).
  reflexivity.
Qed.

(* Task 7b *)

Definition compile (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_aux ae)
  end.

(* Task 7c *)

Theorem compile_satisfies_the_specification :
  specification_of_compile compile.
Proof.
  unfold specification_of_compile, compile.
  intros compile_aux' S_compile_aux' ae.
  Check (there_is_at_most_one_compile_aux compile_aux compile_aux' compile_aux_satisfies_the_specification S_compile_aux' ae).
  rewrite -> (there_is_at_most_one_compile_aux compile_aux compile_aux' compile_aux_satisfies_the_specification S_compile_aux' ae).
  reflexivity.
Qed.

(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
 *)

Fixpoint compile_aux_alt (ae : arithmetic_expression) (a : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
  | Literal n => PUSH n :: a
  | Plus ae1 ae2 => compile_aux_alt ae1 (compile_aux_alt ae2 (ADD :: a))
  | Minus ae1 ae2 => compile_aux_alt ae1 (compile_aux_alt ae2 (SUB :: a))
  end.

Lemma fold_unfold_compile_aux_alt_lit :
  forall (n : nat)
         (a : list byte_code_instruction),
    compile_aux_alt (Literal n) a = PUSH n :: a.
Proof.
  fold_unfold_tactic compile_aux_alt.
Qed.

Lemma fold_unfold_compile_aux_alt_plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_aux_alt (Plus ae1 ae2) a = compile_aux_alt ae1 (compile_aux_alt ae2 (ADD :: a)).
Proof.
  fold_unfold_tactic compile_aux_alt.
Qed.

Lemma fold_unfold_compile_aux_alt_minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_aux_alt (Minus ae1 ae2) a = compile_aux_alt ae1 (compile_aux_alt ae2 (SUB :: a)).
Proof.
  fold_unfold_tactic compile_aux_alt.
Qed.

Definition compile_alt (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_aux_alt ae nil)
  end.

Lemma compile_aux_alt_is_equivalent_to_compile_aux :
  forall (ae : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_aux_alt ae a = compile_aux ae ++ a.
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro a. 
  - rewrite -> fold_unfold_compile_aux_lit.
    rewrite -> fold_unfold_compile_aux_alt_lit. 
    Check (fold_unfold_append_cons (PUSH n) nil a).
    rewrite -> (fold_unfold_append_cons (PUSH n) nil a).
    rewrite -> fold_unfold_append_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> fold_unfold_compile_aux_alt_plus.
    Search ((_) ++ _ = _ ++ _).  
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    Check (fold_unfold_append_cons ADD nil a).
    rewrite -> fold_unfold_append_cons.
    rewrite -> fold_unfold_append_nil. 
    rewrite -> IHae2.
    rewrite -> IHae1.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> fold_unfold_compile_aux_alt_minus.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite -> fold_unfold_append_cons.
    rewrite -> fold_unfold_append_nil.
    rewrite -> IHae2.
    rewrite -> IHae1.
    reflexivity.
Qed.

Theorem compile_alt_satisfies_the_specification :
  specification_of_compile compile_alt.
Proof.
  unfold specification_of_compile, compile_alt.
  intros compile_aux_alt' S_compile_aux_alt' ae.
  unfold compile_aux_alt.
  Check (compile_aux_alt_is_equivalent_to_compile_aux ae nil).
  rewrite -> compile_aux_alt_is_equivalent_to_compile_aux.
  Check (there_is_at_most_one_compile_aux compile_aux compile_aux_alt' compile_aux_satisfies_the_specification S_compile_aux_alt' ae).
  rewrite <- (there_is_at_most_one_compile_aux compile_aux compile_aux_alt' compile_aux_satisfies_the_specification S_compile_aux_alt' ae).
  Search (_ ++ nil = _).
  rewrite -> app_nil_r.
  reflexivity.
Qed.

Theorem compile_is_equivalent_to_compile_alt :
  forall (ae : arithmetic_expression),
    compile (Source_program ae) = compile_alt (Source_program ae).
Proof.
  (*
     this theorem is a corollary of Theorem there_is_at_most_one_compile_function
   *)
  intro ae.
  Check (there_is_at_most_one_compile_function).
  Check (there_is_at_most_one_compile_function compile compile_alt compile_satisfies_the_specification compile_alt_satisfies_the_specification ae).
  exact (there_is_at_most_one_compile_function compile compile_alt compile_satisfies_the_specification compile_alt_satisfies_the_specification ae).
Qed.

(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
 *)

Lemma evaluate_n_lemma :
  forall (ae : arithmetic_expression)
         (n : nat)
         (ds : data_stack),
    evaluate ae = Expressible_nat n -> fetch_decode_execute_loop (compile_aux ae) ds = OK (n :: ds).
Proof.
  induction ae as [l | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intros n ds H_eval_n.
  - rewrite -> fold_unfold_compile_aux_lit.
    rewrite -> fold_unfold_evaluate_Literal in H_eval_n.
    injection H_eval_n as l_is_n.
    rewrite -> l_is_n.
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
    unfold decode_execute.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> fold_unfold_evaluate_Plus in H_eval_n.
    destruct (evaluate ae1) as [n1 | s1] eqn:H_ae1.
    + destruct (evaluate ae2) as [n2 | s2] eqn:H_ae2.
      * injection H_eval_n as n1_plus_n2_is_n.
        assert (IHae1' := IHae1 n1 ds eq_refl).
        assert (IHae2' := IHae2 n2 (n1 :: ds) eq_refl).
        destruct (concatenation (compile_aux ae2) (ADD :: nil) (n1 :: ds)) as [H_concat_2 _].
        assert (H_concat_2' := H_concat_2 (n2 :: n1 :: ds) IHae2').
        destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat_1 _].
        assert (H_concat_1' := H_concat_1 (n1 :: ds) IHae1').
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        Check (fold_unfold_fetch_decode_execute_loop_cons ADD nil (n2 :: n1 :: ds)).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_cons ADD nil (n2 :: n1 :: ds)).
        unfold decode_execute.
        rewrite -> n1_plus_n2_is_n.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        reflexivity.
      * discriminate H_eval_n.
    + discriminate H_eval_n.
  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> fold_unfold_evaluate_Minus in H_eval_n.
    destruct (evaluate ae1) as [n1 | s1] eqn:H_ae1.
    + destruct (evaluate ae2) as [n2 | s2] eqn:H_ae2.
      ++ case (n1 <? n2) eqn:H_underflow.
      * discriminate H_eval_n.
      * injection H_eval_n as n1_minus_n2_is_n.
        assert (IHae1' := IHae1 n1 ds eq_refl).
        assert (IHae2' := IHae2 n2 (n1 :: ds) eq_refl).
        destruct (concatenation (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [H_concat_2 _].
        assert (H_concat_2' := H_concat_2 (n2 :: n1 :: ds) IHae2').
        destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
        assert (H_concat_1' := H_concat_1 (n1 :: ds) IHae1').
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        Check (fold_unfold_fetch_decode_execute_loop_cons SUB nil (n2 :: n1 :: ds)).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_cons SUB nil (n2 :: n1 :: ds)).
        unfold decode_execute.
        rewrite -> H_underflow.
        rewrite -> n1_minus_n2_is_n.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        reflexivity.
      ++ discriminate H_eval_n.
    + discriminate H_eval_n.
Qed.

Lemma evaluate_error_lemma :
  forall (ae : arithmetic_expression)
         (s : string)
         (ds : data_stack),
    evaluate ae = Expressible_msg s -> fetch_decode_execute_loop (compile_aux ae) ds = KO s.
Proof.
  induction ae as [l | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intros s ds H_eval_s.
  - rewrite -> fold_unfold_compile_aux_lit.
    rewrite -> fold_unfold_evaluate_Literal in H_eval_s.
    discriminate H_eval_s.
  - rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> fold_unfold_evaluate_Plus in H_eval_s.
    destruct (evaluate ae1) as [n1 | s1] eqn:H_ae1.
    + destruct (evaluate ae2) as [n2 | s2] eqn:H_ae2.
      * discriminate H_eval_s.
      * injection H_eval_s as s2_is_s.
        rewrite <- s2_is_s.
        destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat_1 _].
        Check (evaluate_n_lemma ae1 n1 ds H_ae1).
        assert (H_concat_1' := H_concat_1 (n1 :: ds) (evaluate_n_lemma ae1 n1 ds H_ae1)).
        destruct (concatenation (compile_aux ae2) (ADD :: nil) (n1 :: ds)) as [_ H_concat_2].
        Check (IHae2 s2 ds eq_refl).
        assert (H_concat_2' := H_concat_2 s2 (IHae2 s2 (n1 :: ds) eq_refl)).
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        reflexivity.
    + injection H_eval_s as s1_is_s.
      rewrite <- s1_is_s.
      destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [_ H_concat_1].
      assert (H_concat_1' := H_concat_1 s1 (IHae1 s1 ds eq_refl)).
      rewrite <- H_concat_1'.
      reflexivity.
  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> fold_unfold_evaluate_Minus in H_eval_s.
    destruct (evaluate ae1) as [n1 | s1] eqn:H_ae1.
    + destruct (evaluate ae2) as [n2 | s2] eqn:H_ae2.
      ++ case (n1 <? n2) eqn:H_underflow.
         * injection H_eval_s as error_is_s.
           destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
           Check (evaluate_n_lemma ae1 n1 ds H_ae1).
           assert (H_concat_1' := H_concat_1 (n1 :: ds) (evaluate_n_lemma ae1 n1 ds H_ae1)).
           destruct (concatenation (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [H_concat_2 _].
           assert (H_concat_2' := H_concat_2 (n2 :: n1 :: ds) (evaluate_n_lemma ae2 n2 (n1 :: ds) H_ae2)).
           rewrite <- H_concat_1'.
           rewrite <- H_concat_2'.
           rewrite -> (fold_unfold_fetch_decode_execute_loop_cons SUB nil (n2 :: n1 :: ds)).
           unfold decode_execute.
           rewrite -> H_underflow.
           rewrite <- error_is_s.
           reflexivity.
         * discriminate H_eval_s.
      ++ injection H_eval_s as s2_is_s.
         rewrite <- s2_is_s.
         destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
         Check (evaluate_n_lemma ae1 n1 ds H_ae1).
         assert (H_concat_1' := H_concat_1 (n1 :: ds) (evaluate_n_lemma ae1 n1 ds H_ae1)).
         destruct (concatenation (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [_ H_concat_2].
         Check (IHae2 s2 ds eq_refl).
         assert (H_concat_2' := H_concat_2 s2 (IHae2 s2 (n1 :: ds) eq_refl)).
         rewrite <- H_concat_1'.
         rewrite <- H_concat_2'.
         reflexivity.
    + injection H_eval_s as s1_is_s.
      rewrite <- s1_is_s.
      destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [_ H_concat_1].
      assert (H_concat_1' := H_concat_1 s1 (IHae1 s1 ds eq_refl)).
      rewrite <- H_concat_1'.
      reflexivity.
Qed.

  (*
combining the previous two lemmas, we have the following lemma:
   *)

Lemma evaluate_ultimate_lemma :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
  (forall (n : nat),
      evaluate ae = Expressible_nat n -> fetch_decode_execute_loop (compile_aux ae) ds = OK (n :: ds)) /\
  (forall (s : string),
      evaluate ae = Expressible_msg s -> fetch_decode_execute_loop (compile_aux ae) ds = KO s).
Proof. 
  induction ae as [l | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro ds; split; intros output H_eval. 
  - rewrite -> fold_unfold_compile_aux_lit.
    rewrite -> fold_unfold_evaluate_Literal in H_eval. 
    injection H_eval as l_is_output.
    rewrite -> l_is_output.
    Check (fold_unfold_fetch_decode_execute_loop_cons (PUSH output) nil ds).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons (PUSH output) nil ds).
    unfold decode_execute.  
    rewrite -> (fold_unfold_fetch_decode_execute_loop_nil (output :: ds)). 
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_lit.
    rewrite -> fold_unfold_evaluate_Literal in H_eval. 
    discriminate H_eval. 
  - rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> fold_unfold_evaluate_Plus in H_eval.   
    destruct (evaluate ae1) as [n1 | s1] eqn:H_ae1.  
    + destruct (evaluate ae2) as [n2 | s2] eqn:H_ae2.
      * injection H_eval as n1_plus_n2_is_output.
        destruct (IHae1 ds) as [IHae1' _].
        destruct (IHae2 (n1 :: ds)) as [IHae2' _].
        assert (IHae1'' := IHae1' n1 eq_refl).
        assert (IHae2'' := IHae2' n2 eq_refl).
        destruct (concatenation (compile_aux ae2) (ADD :: nil) (n1 :: ds)) as [H_concat_2 _].
        assert (H_concat_2' := H_concat_2 (n2 :: n1 :: ds) IHae2'').
        destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat_1 _].
        assert (H_concat_1' := H_concat_1 (n1 :: ds) IHae1'').
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        Check (fold_unfold_fetch_decode_execute_loop_cons ADD nil (n2 :: n1 :: ds)).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_cons ADD nil (n2 :: n1 :: ds)).
        unfold decode_execute.
        rewrite -> n1_plus_n2_is_output.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        reflexivity.
      * discriminate H_eval.
    + discriminate H_eval.
  - rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> fold_unfold_evaluate_Plus in H_eval.
    destruct (evaluate ae1) as [n1 | s1] eqn:H_ae1.
    + destruct (evaluate ae2) as [n2 | s2] eqn:H_ae2.
      * discriminate H_eval.
      * injection H_eval as s2_is_output.
        rewrite <- s2_is_output.
        destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat_1 _].
        destruct (IHae1 ds) as [n1_lemma _].
        Check (n1_lemma n1 eq_refl).
        assert (H_concat_1' := H_concat_1 (n1 :: ds) (n1_lemma n1 eq_refl)).
        destruct (concatenation (compile_aux ae2) (ADD :: nil) (n1 :: ds)) as [_ H_concat_2].
        destruct (IHae2 (n1 :: ds)) as [_ IHae2'].
        Check (IHae2' s2 eq_refl).
        assert (H_concat_2' := H_concat_2 s2  (IHae2' s2 eq_refl)).
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        reflexivity.
    + injection H_eval as s1_is_output.
      rewrite <- s1_is_output.
      destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [_ H_concat_1].
      destruct (IHae1 ds) as [_ IHae1'].
      assert (H_concat_1' := H_concat_1 s1 (IHae1' s1 eq_refl)).
      rewrite <- H_concat_1'.
      reflexivity.
  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> fold_unfold_evaluate_Minus in H_eval.
    destruct (evaluate ae1) as [n1 | s1] eqn:H_ae1.
    + destruct (evaluate ae2) as [n2 | s2] eqn:H_ae2.
      ++ case (n1 <? n2) eqn:H_underflow.
      * discriminate H_eval.
      * injection H_eval as n1_minus_n2_is_output.
        destruct (IHae1 ds) as [IHae1' _].
        destruct (IHae2 (n1 :: ds)) as [IHae2' _].
        assert (IHae1'' := IHae1' n1 eq_refl).
        assert (IHae2'' := IHae2' n2 eq_refl).
        destruct (concatenation (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [H_concat_2 _].
        assert (H_concat_2' := H_concat_2 (n2 :: n1 :: ds) IHae2'').
        destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
        assert (H_concat_1' := H_concat_1 (n1 :: ds) IHae1'').
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        Check (fold_unfold_fetch_decode_execute_loop_cons SUB nil (n2 :: n1 :: ds)).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_cons SUB nil (n2 :: n1 :: ds)).
        unfold decode_execute.
        rewrite -> H_underflow.
        rewrite -> n1_minus_n2_is_output.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        reflexivity.
      ++ discriminate H_eval.
    + discriminate H_eval.
  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> fold_unfold_evaluate_Minus in H_eval.
    destruct (evaluate ae1) as [n1 | s1] eqn:H_ae1.
    + destruct (evaluate ae2) as [n2 | s2] eqn:H_ae2.
      ++ case (n1 <? n2) eqn:H_underflow.
         * injection H_eval as error_is_output.
           destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
           destruct (IHae1 ds) as [n1_lemma _].
           Check (n1_lemma n1 eq_refl).
           assert (H_concat_1' := H_concat_1 (n1 :: ds) (n1_lemma n1 eq_refl)).
           destruct (concatenation (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [H_concat_2 _].
           destruct (IHae2 (n1 :: ds)) as [n2_lemma _].
           Check (n2_lemma n2 eq_refl).
           assert (H_concat_2' := H_concat_2 (n2 :: n1 :: ds) (n2_lemma n2 eq_refl)).
           rewrite <- H_concat_1'.
           rewrite <- H_concat_2'.
           rewrite -> (fold_unfold_fetch_decode_execute_loop_cons SUB nil (n2 :: n1 :: ds)).
           unfold decode_execute.
           rewrite -> H_underflow.
           rewrite <- error_is_output.
           reflexivity. 
         * discriminate H_eval.
      ++ injection H_eval as s2_is_output.
         rewrite <- s2_is_output.
         destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
         destruct (IHae1 ds) as [n1_lemma _].
         Check (n1_lemma n1 eq_refl).
         assert (H_concat_1' := H_concat_1 (n1 :: ds) (n1_lemma n1 eq_refl)).
         destruct (concatenation (compile_aux ae2) (SUB :: nil) (n1 :: ds)) as [_ H_concat_2].
         destruct (IHae2 (n1 :: ds)) as [_ s2_lemma].
         Check (s2_lemma s2 eq_refl).
         assert (H_concat_2' := H_concat_2 s2 (s2_lemma s2 eq_refl)).
         rewrite <- H_concat_1'.
         rewrite <- H_concat_2'.
         reflexivity.
    + injection H_eval as s1_is_output.
      rewrite <- s1_is_output.
      destruct (concatenation (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [_ H_concat_1].
      destruct (IHae1 ds) as [_ s1_lemma].
      Check (s1_lemma s1 eq_refl).
      assert (H_concat_1' := H_concat_1 s1 (s1_lemma s1 eq_refl)).
      rewrite <- H_concat_1'.
      reflexivity.
Qed.

Theorem the_commutative_diagram :
  forall sp : source_program,
    interpret sp = run (compile sp).
Proof.
  intros [ ae ].
  unfold interpret.
  unfold compile.
  unfold run.
  destruct (evaluate ae) as [n | s] eqn : H_evaluate.
  - rewrite -> (evaluate_n_lemma ae n nil).
    reflexivity.
    exact H_evaluate.
  - rewrite -> (evaluate_error_lemma ae s nil).
    reflexivity.
    exact H_evaluate.

  Restart.

  intros [ ae ].
  unfold interpret.
  unfold compile.
  unfold run.
  destruct (evaluate ae) as [n | s] eqn : H_evaluate.
  - destruct (evaluate_ultimate_lemma ae nil) as [n_lemma _].
    rewrite -> (n_lemma n).
    reflexivity.
    exact H_evaluate.
  - destruct (evaluate_ultimate_lemma ae nil) as [_ s_lemma].
    rewrite -> (s_lemma s).
    reflexivity.
    exact H_evaluate.
Qed.

(* ********** *)

(* Byte-code verification:
   the following verifier symbolically executes a byte-code program
   to check whether no underflow occurs during execution
   and whether when the program completes,
   there is one and one only natural number on top of the stack.
   The second argument of verify_aux is a natural number
   that represents the size of the stack.
*)

Fixpoint verify_aux (bcis : list byte_code_instruction) (n : nat) : option nat :=
  match bcis with
    | nil =>
      Some n
    | bci :: bcis' =>
      match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
      end
  end.

Definition verify (p : target_program) : bool :=
  match p with
  | Target_program bcis =>
    match verify_aux bcis 0 with
    | Some n =>
      match n with
      | 1 =>
        true
      | _ =>
        false
      end
    | _ =>
      false
    end
  end.

(* Task 10 (time permitting):
   Prove that the compiler emits code
   that is accepted by the verifier.
 *)

Lemma fold_unfold_verify_aux_nil :
  forall n : nat,
    verify_aux nil n = Some n.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons_push :
  forall (bcis: list byte_code_instruction)
         (n1 n2 : nat),
    verify_aux (PUSH n1 :: bcis) n2 = verify_aux bcis (S n2).
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons_add_O :
  forall (bcis: list byte_code_instruction),
    verify_aux (ADD :: bcis) 0 = None.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons_add_1 :
  forall (bcis: list byte_code_instruction),
    verify_aux (ADD :: bcis) 1 = None.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons_add_S :
  forall (bcis: list byte_code_instruction)
         (n : nat),
    verify_aux (ADD :: bcis) (S (S n)) = verify_aux bcis (S n).
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons_sub_O :
  forall (bcis: list byte_code_instruction),
    verify_aux (SUB :: bcis) 0 = None.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons_sub_1 :
  forall (bcis: list byte_code_instruction),
    verify_aux (SUB :: bcis) 1 = None.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons_sub_S :
  forall (bcis: list byte_code_instruction)
         (n : nat),
    verify_aux (SUB :: bcis) (S (S n)) = verify_aux bcis (S n).
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma nat_option_value_consistency_eq :
  forall n1 n2: nat,
    n1 = n2 <-> Some n1 = Some n2.
Proof.
  intros n1 n2.
  split.
  - intro H_n.
    rewrite H_n.
    reflexivity.
  - intro H_ov.
    injection H_ov as H_v.
    exact H_v.
Qed.

Lemma fold_unfold_verify_aux_S :
  forall (bcis : list byte_code_instruction)
         (n n' : nat),
    verify_aux bcis n = Some n' ->
    verify_aux bcis (S n) = Some (S n').
Proof.
  intro bcis.
  induction bcis as [ | bci' bcis' IHbcis'].
  - intros n n' H.
    rewrite fold_unfold_verify_aux_nil.
    rewrite fold_unfold_verify_aux_nil in H.
    apply nat_option_value_consistency_eq in H.
    apply eq_S in H.
    rewrite H.
    reflexivity.
  - intros n n' H.
    case bci' as [ n'' | | ].
    + rewrite fold_unfold_verify_aux_cons_push in H.
      rewrite fold_unfold_verify_aux_cons_push.
      apply IHbcis'.
      exact H.
    + case n as [ | [ | n''']].
      * rewrite fold_unfold_verify_aux_cons_add_O in H.
        discriminate H.
      * rewrite fold_unfold_verify_aux_cons_add_1 in H.
        discriminate H.
      * rewrite fold_unfold_verify_aux_cons_add_S in H.
        rewrite fold_unfold_verify_aux_cons_add_S.
        apply IHbcis'.
        exact H.
    + case n as [ | [ | n''']].
      * rewrite fold_unfold_verify_aux_cons_sub_O in H.
        discriminate H.
      * rewrite fold_unfold_verify_aux_cons_sub_1 in H.
        discriminate H.
      * rewrite fold_unfold_verify_aux_cons_sub_S in H.
        rewrite fold_unfold_verify_aux_cons_sub_S.
        apply IHbcis'.
        exact H.
Qed.

Lemma verify_aux_combine_two_lists :
  forall (bcis1 bcis2: list byte_code_instruction)
         (n0 n1 n2 : nat),
    verify_aux bcis1 n0 = Some n1 ->
    verify_aux bcis2 n1 = Some n2 ->
    verify_aux (bcis1 ++ bcis2) n0 = Some n2.
Proof.
  intros bcis1 bcis2 n0 n1 n2 H1 H2.
  revert n0 H1.
  induction bcis1 as [ | bci1' bcis1' IHbcis1'].
  - intros n0 H1.
    rewrite fold_unfold_verify_aux_nil in H1.
    rewrite fold_unfold_append_nil.
    rewrite <- nat_option_value_consistency_eq in H1.
    rewrite H1.
    exact H2.
  - intros n0 H1.
    rewrite fold_unfold_append_cons.
    case bci1' as [ n | | ].
    + rewrite fold_unfold_verify_aux_cons_push.
      rewrite fold_unfold_verify_aux_cons_push in H1.
      apply IHbcis1'.
      exact H1.
    + case n0 as [ | [ | n0' ]].
      * rewrite fold_unfold_verify_aux_cons_add_O in H1.
        discriminate H1.
      * rewrite fold_unfold_verify_aux_cons_add_1 in H1.
        discriminate H1.
      * rewrite fold_unfold_verify_aux_cons_add_S in H1.
        rewrite fold_unfold_verify_aux_cons_add_S.
        apply IHbcis1'.
        exact H1.
    + case n0 as [ | [ | n0' ]].
      * rewrite fold_unfold_verify_aux_cons_sub_O in H1.
        discriminate H1.
      * rewrite fold_unfold_verify_aux_cons_sub_1 in H1.
        discriminate H1.
      * rewrite fold_unfold_verify_aux_cons_sub_S in H1.
        rewrite fold_unfold_verify_aux_cons_sub_S.
        apply IHbcis1'.
        exact H1.

  Restart.

  (* alternative proof without using lemma fold_unfold_verify_aux_S *)

  intros bcis1 bcis2 n0 n1 n2 H1 H2.
  revert n0 H1.
  induction bcis1 as [ | bci1' bcis1' IHbcis1'].
  - intros n0 H1.
    rewrite fold_unfold_verify_aux_nil in H1.
    rewrite fold_unfold_append_nil.
    rewrite <- nat_option_value_consistency_eq in H1.
    rewrite H1.
    exact H2.
  - intros n0 H1.
    rewrite fold_unfold_append_cons.
    case bci1' as [ n | | ].
    + rewrite fold_unfold_verify_aux_cons_push.
      rewrite fold_unfold_verify_aux_cons_push in H1.
      apply IHbcis1'.
      exact H1.
    + case n0 as [ | [ | n0' ]].
      * rewrite fold_unfold_verify_aux_cons_add_O in H1.
        discriminate H1.
      * rewrite fold_unfold_verify_aux_cons_add_1 in H1.
        discriminate H1.
      * rewrite fold_unfold_verify_aux_cons_add_S in H1.
        rewrite fold_unfold_verify_aux_cons_add_S.
        apply IHbcis1'.
        exact H1.
    + case n0 as [ | [ | n0' ]].
      * rewrite fold_unfold_verify_aux_cons_sub_O in H1.
        discriminate H1.
      * rewrite fold_unfold_verify_aux_cons_sub_1 in H1.
        discriminate H1.
      * rewrite fold_unfold_verify_aux_cons_sub_S in H1.
        rewrite fold_unfold_verify_aux_cons_sub_S.
        apply IHbcis1'.
        exact H1.
Qed.

(* alternative proof of the above lemma, stated slightly differently. *)

Lemma verify_aux_combine_two_lists_alt :
  forall (bcis1 bcis2: list byte_code_instruction)
         (n0 n1 : nat),
    verify_aux bcis1 n0 = Some n1 ->
    verify_aux bcis2 n1 = verify_aux (bcis1 ++ bcis2) n0.
Proof.
  intros bcis1 bcis2 n0 n1 H.
  revert n0 H.
  induction bcis1 as [ | bci1' bcis1' IHbcis1'].
  - intros n0 H.
    rewrite fold_unfold_verify_aux_nil in H.
    rewrite fold_unfold_append_nil. 
    rewrite <- nat_option_value_consistency_eq in H.
    rewrite H.
    reflexivity.
  - intros n0 H.
    rewrite fold_unfold_append_cons.
    case bci1' as [ n | | ].
    + rewrite fold_unfold_verify_aux_cons_push.
      rewrite fold_unfold_verify_aux_cons_push in H.
      apply IHbcis1'.
      exact H.
    + case n0 as [ | [ | n0' ]].
      * rewrite fold_unfold_verify_aux_cons_add_O in H.
        discriminate H.
      * rewrite fold_unfold_verify_aux_cons_add_1 in H.
        discriminate H.
      * rewrite fold_unfold_verify_aux_cons_add_S in H.
        rewrite fold_unfold_verify_aux_cons_add_S.
        apply IHbcis1'.
        exact H.
    + case n0 as [ | [ | n0' ]].
      * rewrite fold_unfold_verify_aux_cons_sub_O in H.
        discriminate H.
      * rewrite fold_unfold_verify_aux_cons_sub_1 in H.
        discriminate H.
      * rewrite fold_unfold_verify_aux_cons_sub_S in H.
        rewrite fold_unfold_verify_aux_cons_sub_S.
        apply IHbcis1'.
        exact H.
Qed.

Lemma the_compiler_emits_well_behaved_code_aux :
  forall (ae : arithmetic_expression)
         (n : nat),
    verify_aux (compile_aux ae) n = Some (S n).
Proof.
  intros ae.
  induction ae as [n' | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - intro n.
    rewrite fold_unfold_compile_aux_lit.
    rewrite fold_unfold_verify_aux_cons_push.
    rewrite fold_unfold_verify_aux_nil.
    reflexivity.
  - intro n.
    rewrite fold_unfold_compile_aux_plus.
    remember (compile_aux ae1) as bcis1.
    remember (compile_aux ae2) as bcis2.
    assert (H_concat := (verify_aux_combine_two_lists bcis1 bcis2 n (S n) (S (S n))) (IHae1 n) (IHae2 (S n))).
    assert (H_add := fold_unfold_verify_aux_cons_add_S nil n).
    rewrite app_assoc.
    exact ((verify_aux_combine_two_lists (bcis1 ++ bcis2) (ADD :: nil) n (S (S n)) (S n)) H_concat H_add).
  - intro n.
    rewrite fold_unfold_compile_aux_minus.
    remember (compile_aux ae1) as bcis1.
    remember (compile_aux ae2) as bcis2.
    assert (H_concat := (verify_aux_combine_two_lists bcis1 bcis2 n (S n) (S (S n))) (IHae1 n) (IHae2 (S n))).
    assert (H_sub := fold_unfold_verify_aux_cons_sub_S nil n).
    rewrite app_assoc.
    exact ((verify_aux_combine_two_lists (bcis1 ++ bcis2) (SUB :: nil) n (S (S n)) (S n)) H_concat H_sub).
Qed.

Theorem the_compiler_emits_well_behaved_code :
  forall sp: source_program,
    verify (compile sp) = true.
Proof.
  intros [ae].
  unfold verify, compile.
  rewrite the_compiler_emits_well_behaved_code_aux.
  reflexivity.
Qed.

(* Subsidiary question:
   What is the practical consequence of this theorem?
*)

(* ********** *)

(* Task 11:

   a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.
 *)


Inductive Expressible_value_m : Type :=
| Expressible_nat_m : arithmetic_expression -> Expressible_value_m
| Expressible_msg_m : string -> Expressible_value_m.
                            
                                  
Definition specification_of_evaluate_m (evaluate_m : arithmetic_expression -> Expressible_value_m) :=
  (forall n : nat,
     evaluate_m (Literal n) = Expressible_nat_m (Literal n))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate_m ae1 = Expressible_msg_m s1 ->
       evaluate_m (Plus ae1 ae2) = Expressible_msg_m s1)
   /\
   (forall (ae1 ae2 ae1' : arithmetic_expression)
           (s2 : string),
       evaluate_m ae1 = Expressible_nat_m ae1' ->
       evaluate_m ae2 = Expressible_msg_m s2 ->
       evaluate_m (Plus ae1 ae2) = Expressible_msg_m s2)
   /\
   (forall (ae1 ae2 ae1' ae2' : arithmetic_expression),
       evaluate_m ae1 = Expressible_nat_m ae1' ->
       evaluate_m ae2 = Expressible_nat_m ae2' ->
       evaluate_m (Plus ae1 ae2) = Expressible_nat_m (Plus ae1'  ae2')))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
            (s1 : string),
       evaluate_m ae1 = Expressible_msg_m s1 ->
       evaluate_m (Minus ae1 ae2) = Expressible_msg_m s1)
   /\
   (forall (ae1 ae2 ae1' : arithmetic_expression)
           (s2 : string),
       evaluate_m ae1 = Expressible_nat_m ae1' ->
       evaluate_m ae2 = Expressible_msg_m s2 ->
       evaluate_m (Minus ae1 ae2) = Expressible_msg_m s2)
   /\
   (forall (ae1 ae2 ae1' ae2' : arithmetic_expression),
       evaluate_m ae1 = Expressible_nat_m ae1' ->
       evaluate_m ae2 = Expressible_nat_m ae2' ->
       evaluate_m (Minus ae1 ae2) = Expressible_nat_m (Minus ae1' ae2'))).

Fixpoint evaluate_m (ae : arithmetic_expression) : Expressible_value_m :=
 match ae with
  | Literal n =>
    Expressible_nat_m (Literal n)
  | Plus ae1 ae2 =>
    match evaluate_m ae1 with
    | Expressible_nat_m ae1' =>
      match evaluate_m ae2 with
      | Expressible_nat_m ae2' =>
        Expressible_nat_m (Plus ae1' ae2')
      | Expressible_msg_m s =>
        Expressible_msg_m s
      end
    | Expressible_msg_m s =>
      Expressible_msg_m s
    end
  | Minus ae1 ae2 =>
    match evaluate_m ae1 with
    | Expressible_nat_m ae1' =>
      match evaluate_m ae2 with
      | Expressible_nat_m ae2' =>
        Expressible_nat_m (Minus ae1' ae2')
      | Expressible_msg_m s =>
        Expressible_msg_m s
      end
    | Expressible_msg_m s =>
      Expressible_msg_m s
    end
 end.

Lemma fold_unfold_evaluate_m_Literal :
  forall n : nat,
    evaluate_m (Literal n) = Expressible_nat_m  (Literal n).
Proof.
  fold_unfold_tactic evaluate_m.
Qed.

Lemma fold_unfold_evaluate_m_Plus :
  forall (ae1 ae2 : arithmetic_expression),
   evaluate_m (Plus ae1 ae2) =
    match evaluate_m ae1 with
    | Expressible_nat_m  ae1' =>
      match evaluate_m ae2 with
      | Expressible_nat_m  ae2' =>
        Expressible_nat_m  (Plus ae1' ae2')
      | Expressible_msg_m s =>
        Expressible_msg_m s
      end
    | Expressible_msg_m s =>
      Expressible_msg_m s
    end.
Proof.
  fold_unfold_tactic evaluate_m.
Qed.

Lemma fold_unfold_evaluate_m_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_m (Minus ae1 ae2) =
    match evaluate_m ae1 with
    | Expressible_nat_m  ae1' =>
      match evaluate_m ae2 with
      | Expressible_nat_m  ae2' =>
        Expressible_nat_m  (Minus ae1' ae2')
      | Expressible_msg_m s =>
        Expressible_msg_m s
      end
    | Expressible_msg_m s =>
      Expressible_msg_m s
    end.
Proof.
  fold_unfold_tactic evaluate_m.
Qed.

Definition specification_of_interpret_m (interpret_m : source_program -> Expressible_value_m) :=
  forall evaluate_m : arithmetic_expression -> Expressible_value_m,
    specification_of_evaluate_m evaluate_m ->
    forall ae : arithmetic_expression,
      interpret_m (Source_program ae) = evaluate_m ae.

Definition interpret_m (sp : source_program) : Expressible_value_m :=
  match sp with
  | Source_program ae =>
    evaluate_m ae
  end.


(*
   b. Write a Magritte interpreter for the target language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.
 *)

(* Recall: Definition of Target programs: *)
(* Magritte Byte-code instructions: *)

(* Magritte Data stack: *)

Definition data_stack_m := list arithmetic_expression.

(* ********** *)

Inductive result_of_decoding_and_execution_m : Type :=
| OK_m : data_stack_m -> result_of_decoding_and_execution_m
| KO_m : string -> result_of_decoding_and_execution_m.

Definition specification_of_decode_execute_m (decode_execute_m : byte_code_instruction -> data_stack_m -> result_of_decoding_and_execution_m) :=
  (forall (n: nat)
          (ds : data_stack_m),
     decode_execute_m (PUSH n) ds = OK_m ((Literal n) :: ds))
  /\
  ((decode_execute_m ADD nil = KO_m "ADD: stack underflow")
   /\
   (forall (ae1 : arithmetic_expression),
       decode_execute_m ADD (ae1 :: nil) = KO_m "ADD: stack underflow")
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (ds : data_stack_m),
       decode_execute_m ADD (ae2 :: ae1 :: ds) = OK_m ((Plus ae1 ae2) :: ds)))
  /\
  ((decode_execute_m SUB nil = KO_m "SUB: stack underflow")
   /\
   (forall (ae2 : arithmetic_expression),
       decode_execute_m SUB (ae2 :: nil) = KO_m "SUB: stack underflow")
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (ds : data_stack_m),
       decode_execute_m SUB (ae2 :: ae1 :: ds) = OK_m ((Minus ae1 ae2) :: ds))).

Definition decode_execute_m (bcis : byte_code_instruction) (ds : data_stack_m) : result_of_decoding_and_execution_m :=
  match bcis with
  | PUSH n =>
    OK_m ((Literal n) :: ds)
  | ADD =>
    match ds with
    | nil =>
      KO_m "ADD: stack underflow"
    | ae2 :: nil =>
      KO_m "ADD: stack underflow"
    | ae2 :: ae1 :: ds =>
      OK_m ((Plus ae1 ae2) :: ds)
    end
  | SUB =>
    match ds with
    | nil =>
      KO_m "SUB: stack underflow"
    | ae2 :: nil =>
      KO_m "SUB: stack underflow"
    | ae2 :: ae1 :: ds =>
      OK_m ((Minus ae1 ae2) :: ds)
    end
  end.


(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop_m (fetch_decode_execute_loop_m : list byte_code_instruction -> data_stack_m -> result_of_decoding_and_execution_m) :=
  forall decode_execute_m : byte_code_instruction -> data_stack_m -> result_of_decoding_and_execution_m,
    specification_of_decode_execute_m decode_execute_m ->
    (forall ds : data_stack_m,
        fetch_decode_execute_loop_m nil ds = OK_m ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack_m),
        decode_execute_m bci ds = OK_m ds' ->
        fetch_decode_execute_loop_m (bci :: bcis') ds =
        fetch_decode_execute_loop_m bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack_m)
            (s : string),
        decode_execute_m bci ds = KO_m s ->
        fetch_decode_execute_loop_m (bci :: bcis') ds =
        KO_m s).
 
Fixpoint fetch_decode_execute_loop_m (bcis : list byte_code_instruction) (ds : data_stack_m) : result_of_decoding_and_execution_m :=
  match bcis with
  | nil => OK_m ds
  | bci :: bcis' =>
    match (decode_execute_m bci ds) with
    | OK_m ds' => fetch_decode_execute_loop_m bcis' ds'
    | KO_m s => KO_m s
    end
  end.

Lemma fold_unfold_fetch_decode_execute_loop_m_nil :
  forall ds : data_stack_m,
    fetch_decode_execute_loop_m nil ds = OK_m ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_m.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_m_cons :
  forall (bci: byte_code_instruction)
         (bcis': list byte_code_instruction)
         (ds : data_stack_m),
    fetch_decode_execute_loop_m (bci :: bcis') ds =
    match decode_execute_m bci ds with
    | OK_m ds' => fetch_decode_execute_loop_m bcis' ds'
    | KO_m s => KO_m s
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_m.
Qed.  

    
(* ********** *)

(* Specification of run: *)

Definition specification_of_run_m (run_m : target_program -> Expressible_value_m) :=
  forall fetch_decode_execute_loop_m : list byte_code_instruction -> data_stack_m -> result_of_decoding_and_execution_m,
    specification_of_fetch_decode_execute_loop_m fetch_decode_execute_loop_m ->
    (forall (bcis : list byte_code_instruction),
       fetch_decode_execute_loop_m bcis nil = OK_m nil ->
       run_m (Target_program bcis) = Expressible_msg_m "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (ae : arithmetic_expression),
       fetch_decode_execute_loop_m bcis nil = OK_m (ae :: nil) ->
       run_m (Target_program bcis) = Expressible_nat_m  ae)
    /\
    (forall (bcis : list byte_code_instruction)
            (ae ae' : arithmetic_expression)
            (ds'' : data_stack_m),
       fetch_decode_execute_loop_m bcis nil = OK_m (ae :: ae' :: ds'') ->
       run_m (Target_program bcis) = Expressible_msg_m "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop_m bcis nil = KO_m s ->
       run_m (Target_program bcis) = Expressible_msg_m s).

Definition run_m (tp : target_program) : Expressible_value_m :=
  match tp with
  | Target_program bcis =>
    match (fetch_decode_execute_loop_m bcis nil) with
    | OK_m nil =>
      Expressible_msg_m "no result on the data stack"
    | OK_m (ae :: nil) =>
      Expressible_nat_m  ae
    | OK_m (ae :: ae' :: ds'') =>
      Expressible_msg_m "too many results on the data stack"
    | KO_m s =>
      Expressible_msg_m s
    end
  end.

(*
   c. Prove that interpreting an arithmetic expression with the Magritte source interpreter
      gives the same result as first compiling it and then executing the compiled program
      with the Magritte target interpreter over an empty data stack.
*)
  
(* original compiler: push add -> arithmetic_expression *)


Theorem concatenation_m :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds: data_stack_m) ,
  (forall (ds': data_stack_m),
    (fetch_decode_execute_loop_m bcis1 ds) = OK_m ds'
    ->
    (fetch_decode_execute_loop_m bcis2 ds') = (fetch_decode_execute_loop_m (bcis1 ++ bcis2) ds))
  /\
  (forall (s' : string),
      (fetch_decode_execute_loop_m bcis1 ds) = KO_m s'
      ->
      KO_m s' = (fetch_decode_execute_loop_m (bcis1 ++ bcis2) ds)).
Proof.
  unfold specification_of_fetch_decode_execute_loop_m.
  intro bcis1.
  induction bcis1 as [ | bci bcis1' IHbcis1 ].
  + intros bcis2 ds.
    split.
  - intros ds' H_OK_nil.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_m_nil) in H_OK_nil.
    rewrite -> (fold_unfold_append_nil bcis2).
    injection H_OK_nil.
    intro H_equal.
    rewrite -> (H_equal).
    reflexivity. 
  - intros s' H_KO_nil. 
    rewrite -> (fold_unfold_fetch_decode_execute_loop_m_nil) in H_KO_nil.
    discriminate H_KO_nil.
  + intros bcis2 ds.
    split.
    - intros ds' H_OK_cons.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_m_cons) in H_OK_cons.
      Check (fold_unfold_append_cons). 
      rewrite -> (fold_unfold_append_cons bci bcis1' bcis2).
      Check (fold_unfold_fetch_decode_execute_loop_m_cons).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_m_cons bci (bcis1' ++ bcis2) ds).
      destruct (decode_execute_m bci ds) as [ds'' | s'].
      -- destruct (IHbcis1 bcis2 ds'') as [IHds IHs].
         rewrite (IHds ds' H_OK_cons).
         reflexivity.
      -- discriminate.
    - intros s' H_KO_cons.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_m_cons) in H_KO_cons.
      Check (fold_unfold_append_cons). 
      rewrite -> (fold_unfold_append_cons bci bcis1' bcis2).
      Check (fold_unfold_fetch_decode_execute_loop_m_cons).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_m_cons bci (bcis1' ++ bcis2) ds).
      destruct (decode_execute_m bci ds) as [ds'' | s''].
      -- destruct (IHbcis1 bcis2 ds'') as [IHds IHs].
         rewrite (IHs s' H_KO_cons).
         reflexivity.
      -- symmetry.
         exact H_KO_cons.
Qed.

Lemma evaluate_m_lemma :
  forall (ae ae': arithmetic_expression)
         (ds : data_stack_m),
    evaluate_m ae = Expressible_nat_m  ae' -> fetch_decode_execute_loop_m (compile_aux ae) ds = OK_m (ae' :: ds).
Proof. 
  induction ae as [l | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intros ae' ds H_eval_m.
  - rewrite -> fold_unfold_compile_aux_lit.
    rewrite -> fold_unfold_evaluate_m_Literal in H_eval_m.
    rewrite -> fold_unfold_fetch_decode_execute_loop_m_cons.
    unfold decode_execute_m.
    injection H_eval_m as l_is_n.
    rewrite -> l_is_n.
    rewrite -> fold_unfold_fetch_decode_execute_loop_m_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_plus. 
    rewrite -> (fold_unfold_evaluate_m_Plus) in H_eval_m.
    destruct (evaluate_m ae1) as [ae1' | s1] eqn:H_ae1. 
    + destruct (evaluate_m ae2) as [ae2' | s2] eqn:H_ae2.
      * injection H_eval_m as ae1'_plus_ae2'.
        assert (IHae1' := IHae1 ae1' ds eq_refl).
        assert (IHae2' := IHae2 ae2' (ae1' :: ds) eq_refl).
        destruct (concatenation_m (compile_aux ae2) (ADD :: nil) (ae1' :: ds)) as [H_concat_2 _].
        assert (H_concat_2' := H_concat_2 (ae2' :: ae1' :: ds) IHae2').
        destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat_1 _].
        assert (H_concat_1' := H_concat_1 (ae1' :: ds) IHae1').
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        Check (fold_unfold_fetch_decode_execute_loop_m_cons ADD nil (ae2' :: ae1' :: ds)).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_m_cons ADD nil (ae2' :: ae1' :: ds)).
        unfold decode_execute_m.
        rewrite -> ae1'_plus_ae2'.
        rewrite -> fold_unfold_fetch_decode_execute_loop_m_nil.
        reflexivity. 
      * discriminate H_eval_m.
    + discriminate H_eval_m. 
  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> fold_unfold_evaluate_m_Minus in H_eval_m.
    destruct (evaluate_m ae1) as [ae1' | s1] eqn:H_ae1.
    + destruct (evaluate_m ae2) as [ae2' | s2] eqn:H_ae2.
      ++
      * injection H_eval_m as ae1'_minus_ae2'.
        assert (IHae1' := IHae1 ae1' ds eq_refl).
        assert (IHae2' := IHae2 ae2' (ae1' :: ds) eq_refl).
        destruct (concatenation_m (compile_aux ae2) (SUB :: nil) (ae1' :: ds)) as [H_concat_2 _].
        assert (H_concat_2' := H_concat_2 (ae2' :: ae1' :: ds) IHae2').
        destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
        assert (H_concat_1' := H_concat_1 (ae1' :: ds) IHae1').
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        Check (fold_unfold_fetch_decode_execute_loop_m_cons SUB nil (ae2' :: ae1' :: ds)).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_m_cons SUB nil (ae2' :: ae1' :: ds)).
        unfold decode_execute_m.
        rewrite -> ae1'_minus_ae2'.
        rewrite -> fold_unfold_fetch_decode_execute_loop_m_nil.
        reflexivity.
      ++ discriminate H_eval_m.
    + discriminate H_eval_m.
Qed. 

Lemma evaluate_error_lemma_m :
  forall (ae : arithmetic_expression)
         (s : string)
         (ds : data_stack_m),
    evaluate_m ae = Expressible_msg_m s -> fetch_decode_execute_loop_m (compile_aux ae) ds = KO_m s.
Proof.
  induction ae as [l | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intros s ds H_eval_s.
  - rewrite -> fold_unfold_compile_aux_lit.
    rewrite -> fold_unfold_evaluate_m_Literal in H_eval_s.
    discriminate H_eval_s.
  - rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> fold_unfold_evaluate_m_Plus in H_eval_s.
    destruct (evaluate_m ae1) as [ae1' | s1] eqn:H_ae1.
    + destruct (evaluate_m ae2) as [ae2' | s2] eqn:H_ae2.
      * discriminate H_eval_s.
      * injection H_eval_s as s2_is_s.
        rewrite <- s2_is_s.
        destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat_1 _].
        Check (evaluate_m_lemma ae1 ae1' ds H_ae1).
        assert (H_concat_1' := H_concat_1 (ae1' :: ds) (evaluate_m_lemma ae1 ae1' ds H_ae1)).
        destruct (concatenation_m (compile_aux ae2) (ADD :: nil) (ae1' :: ds)) as [_ H_concat_2].
        Check (IHae2 s2 ds eq_refl).
        assert (H_concat_2' := H_concat_2 s2 (IHae2 s2 (ae1' :: ds) eq_refl)).
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        reflexivity.
    + injection H_eval_s as s1_is_s.
      rewrite <- s1_is_s.
      destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [_ H_concat_1].
      assert (H_concat_1' := H_concat_1 s1 (IHae1 s1 ds eq_refl)).
      rewrite <- H_concat_1'.
      reflexivity.
  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> fold_unfold_evaluate_m_Minus in H_eval_s.
    destruct (evaluate_m ae1) as [ae1' | s1] eqn:H_ae1.
    + destruct (evaluate_m ae2) as [ae2' | s2] eqn:H_ae2.
      ++
         * discriminate H_eval_s.
      ++ injection H_eval_s as s2_is_s.
         rewrite <- s2_is_s.
         destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
         Check (evaluate_m_lemma ae1 ae1' ds H_ae1).
         assert (H_concat_1' := H_concat_1 (ae1' :: ds) (evaluate_m_lemma ae1 ae1' ds H_ae1)).
         destruct (concatenation_m (compile_aux ae2) (SUB :: nil) (ae1' :: ds)) as [_ H_concat_2].
         Check (IHae2 s2 ds eq_refl).
         assert (H_concat_2' := H_concat_2 s2 (IHae2 s2 (ae1' :: ds) eq_refl)).
         rewrite <- H_concat_1'.
         rewrite <- H_concat_2'.
         reflexivity.
    + injection H_eval_s as s1_is_s.
      rewrite <- s1_is_s.
      destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [_ H_concat_1].
      assert (H_concat_1' := H_concat_1 s1 (IHae1 s1 ds eq_refl)).
      rewrite <- H_concat_1'.
      reflexivity.
 Qed.

Lemma evaluate_ultimate_lemma_m :
  forall (ae : arithmetic_expression)
         (ds : data_stack_m),
    (forall (ae' : arithmetic_expression),
      evaluate_m ae = Expressible_nat_m ae' -> fetch_decode_execute_loop_m (compile_aux ae) ds = OK_m (ae' :: ds)) /\
  (forall (s : string),
      evaluate_m ae = Expressible_msg_m s -> fetch_decode_execute_loop_m (compile_aux ae) ds = KO_m s).
Proof.
  induction ae as [ l | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro ds; split; intros output H_eval.
  - rewrite -> fold_unfold_compile_aux_lit.
    rewrite -> fold_unfold_evaluate_m_Literal in H_eval.
    injection H_eval as l_is_output.
    rewrite -> fold_unfold_fetch_decode_execute_loop_m_cons.
    unfold decode_execute_m.
    rewrite -> l_is_output.
    rewrite -> fold_unfold_fetch_decode_execute_loop_m_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_lit.
    rewrite -> fold_unfold_evaluate_m_Literal in H_eval.
    discriminate H_eval.
  - rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> fold_unfold_evaluate_m_Plus in H_eval.
    destruct (evaluate_m ae1) as [ae1' | s1] eqn:H_ae1.
    + destruct (evaluate_m ae2) as [ae2' | s2] eqn:H_ae2.
      * injection H_eval as ae1'_plus_ae2'.
        destruct (IHae1 ds) as [IHae1' _].
        destruct (IHae2 (ae1' :: ds)) as [IHae2' _].
        assert (IHae1'' := IHae1' ae1' eq_refl).
        assert (IHae2'' := IHae2' ae2' eq_refl).
        destruct (concatenation_m (compile_aux ae2) (ADD :: nil) (ae1' :: ds)) as [H_concat_2 _].
        assert (H_concat_2' := H_concat_2 (ae2' :: ae1' :: ds) IHae2'').
        destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat_1 _].
        assert (H_concat_1' := H_concat_1 (ae1' :: ds) IHae1'').
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        Check (fold_unfold_fetch_decode_execute_loop_m_cons ADD nil (ae2' :: ae1' :: ds)).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_m_cons ADD nil (ae2' :: ae1' :: ds)).
        unfold decode_execute_m.
        rewrite -> ae1'_plus_ae2'.
        rewrite -> fold_unfold_fetch_decode_execute_loop_m_nil.
        reflexivity.
      * discriminate H_eval.
    + discriminate H_eval.
  - rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> fold_unfold_evaluate_m_Plus in H_eval.
    destruct (evaluate_m ae1) as [ae1' | s1] eqn:H_ae1.
    + destruct (evaluate_m ae2) as [ae2' | s2] eqn:H_ae2.
      * discriminate H_eval.
      * injection H_eval as s2_is_output.
        rewrite <- s2_is_output.
        destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [H_concat_1 _].
        destruct (IHae1 ds) as [ae1'_lemma _].
        Check (ae1'_lemma ae1' eq_refl).
        assert (H_concat_1' := H_concat_1 (ae1' :: ds) (ae1'_lemma ae1' eq_refl)).
        destruct (concatenation_m (compile_aux ae2) (ADD :: nil) (ae1' :: ds)) as [_ H_concat_2].
        destruct (IHae2 (ae1' :: ds)) as [_ IHae2'].
        Check (IHae2' s2 eq_refl).
        assert (H_concat_2' := H_concat_2 s2  (IHae2' s2 eq_refl)).
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        reflexivity.
    + injection H_eval as s1_is_output.
      rewrite <- s1_is_output.
      destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds) as [_ H_concat_1].
      destruct (IHae1 ds) as [_ IHae1'].
      assert (H_concat_1' := H_concat_1 s1 (IHae1' s1 eq_refl)).
      rewrite <- H_concat_1'.
      reflexivity.
  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> fold_unfold_evaluate_m_Minus in H_eval.
    destruct (evaluate_m ae1) as [ae1' | s1] eqn:H_ae1.
    + destruct (evaluate_m ae2) as [ae2' | s2] eqn:H_ae2.
      * injection H_eval as ae1'_minus_ae2'_is_output.
        destruct (IHae1 ds) as [IHae1' _].
        destruct (IHae2 (ae1' :: ds)) as [IHae2' _].
        assert (IHae1'' := IHae1' ae1' eq_refl).
        assert (IHae2'' := IHae2' ae2' eq_refl).
        destruct (concatenation_m (compile_aux ae2) (SUB :: nil) (ae1' :: ds)) as [H_concat_2 _].
        assert (H_concat_2' := H_concat_2 (ae2' :: ae1' :: ds) IHae2'').
        destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
        assert (H_concat_1' := H_concat_1 (ae1' :: ds) IHae1'').
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        Check (fold_unfold_fetch_decode_execute_loop_m_cons SUB nil (ae2' :: ae1' :: ds)).
        rewrite -> (fold_unfold_fetch_decode_execute_loop_m_cons SUB nil (ae2' :: ae1' :: ds)).
        unfold decode_execute_m.
        rewrite -> ae1'_minus_ae2'_is_output.
        rewrite -> fold_unfold_fetch_decode_execute_loop_m_nil.
        reflexivity.
        * discriminate H_eval.
    + discriminate H_eval.
  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> fold_unfold_evaluate_m_Minus in H_eval.
    destruct (evaluate_m ae1) as [ae1' | s1] eqn:H_ae1.
    + destruct (evaluate_m ae2) as [ae2' | s2] eqn:H_ae2.
      * discriminate H_eval.
      * injection H_eval as s2_is_output.
        rewrite <- s2_is_output.
        destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [H_concat_1 _].
        destruct (IHae1 ds) as [ae1'_lemma _].
        Check (ae1'_lemma ae1' eq_refl).
        assert (H_concat_1' := H_concat_1 (ae1' :: ds) (ae1'_lemma ae1' eq_refl)).
        destruct (concatenation_m (compile_aux ae2) (SUB :: nil) (ae1' :: ds)) as [_ H_concat_2].
        destruct (IHae2 (ae1' :: ds)) as [_ s2_lemma].
        Check (s2_lemma s2 eq_refl).
        assert (H_concat_2' := H_concat_2 s2 (s2_lemma s2 eq_refl)).
        rewrite <- H_concat_1'.
        rewrite <- H_concat_2'.
        reflexivity.
    + injection H_eval as s1_is_output.
      rewrite <- s1_is_output.
      destruct (concatenation_m (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds) as [_ H_concat_1].
      destruct (IHae1 ds) as [_ s1_lemma].
      Check (s1_lemma s1 eq_refl).
      assert (H_concat_1' := H_concat_1 s1 (s1_lemma s1 eq_refl)).
      rewrite <- H_concat_1'.
      reflexivity.
Qed.     

      
Theorem the_commutative_diagram_m :
  forall sp : source_program,
    interpret_m sp = run_m (compile sp).
Proof. 
  intros [ ae ].
  unfold interpret_m.
  unfold compile.
  unfold run_m.
  destruct (evaluate_m ae) as [ae' | s] eqn : H_evaluate.  
  - rewrite -> (evaluate_m_lemma ae ae' nil).
    reflexivity. 
    exact H_evaluate.
  - rewrite -> (evaluate_error_lemma_m ae s nil).
    reflexivity.
    exact H_evaluate.

  Restart.

  intros [ ae ].
  unfold interpret_m.
  unfold compile.
  unfold run_m.
  destruct (evaluate_m ae) as [ae' | s] eqn : H_evaluate.
  - destruct (evaluate_ultimate_lemma_m ae nil) as [ae'_lemma _].
    rewrite -> (ae'_lemma ae').
    reflexivity.
    exact H_evaluate.
  - destruct (evaluate_ultimate_lemma_m ae nil) as [_ s_lemma].
    rewrite -> (s_lemma s).
    reflexivity.
    exact H_evaluate.
Qed.

 
(*
   d. Prove that the Magritte target interpreter is (essentially)
      a left inverse of the compiler, i.e., it is a decompiler.
*)

Proposition about_evaluate_m :
  forall ae : arithmetic_expression,
    evaluate_m ae = Expressible_nat_m ae.
Proof.
  induction ae as [ l | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - rewrite -> (fold_unfold_evaluate_m_Literal l).
    reflexivity.
  - rewrite -> (fold_unfold_evaluate_m_Plus ae1 ae2 ).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - rewrite -> (fold_unfold_evaluate_m_Minus ae1 ae2).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.  

Theorem decompile :
  forall ae : arithmetic_expression,
    run_m (compile (Source_program ae)) = Expressible_nat_m ae.
(* 
note to self:
run_m compile ae => ae 
run_m is a left inverse of compile 
run_m is a decompiler 
*)
Proof.
  intro ae.
  Check (the_commutative_diagram_m (Source_program ae)).
  rewrite <- (the_commutative_diagram_m (Source_program ae)).
  unfold interpret_m.
  Check (about_evaluate_m).
  apply (about_evaluate_m).
Qed.


Definition Expressible_value_m' := arithmetic_expression.

Definition specification_of_evaluate_m' (evaluate_m' : arithmetic_expression -> arithmetic_expression) :=
  (forall n : nat,
     evaluate_m' (Literal n) = Literal n)
  /\
  (forall (ae1 ae2 ae1' ae2' : arithmetic_expression),
      evaluate_m' ae1 = ae1' ->
      evaluate_m' ae2 = ae2' ->
      evaluate_m' (Plus ae1 ae2) = Plus ae1' ae2')
  /\
  (forall (ae1 ae2 ae1' ae2' : arithmetic_expression),
      evaluate_m' ae1 = ae1' ->
      evaluate_m' ae2 = ae2' ->
      evaluate_m' (Minus ae1 ae2) = Minus ae1' ae2').


Fixpoint evaluate_m' (ae : arithmetic_expression) : Expressible_value_m' :=
 match ae with
  | Literal n =>
    (Literal n)
  | Plus ae1 ae2 =>
    match evaluate_m' ae1 with
    | ae1' =>
      match evaluate_m' ae2 with
      | ae2' =>
         (Plus ae1' ae2')
      end
    end
  | Minus ae1 ae2 =>
    match evaluate_m' ae1 with
    |  ae1' =>
      match evaluate_m' ae2 with
      | ae2' =>
          (Minus ae1' ae2')
      end
    end
 end.

Lemma fold_unfold_evaluate_m'_Literal :
  forall n : nat,
    evaluate_m' (Literal n) = (Literal n).
Proof.
  fold_unfold_tactic evaluate_m'.
Qed.

Lemma fold_unfold_evaluate_m'_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_m' (Plus ae1 ae2) =
    match evaluate_m' ae1 with
    | ae1' =>
      match evaluate_m' ae2 with
      | ae2' =>
        (Plus ae1' ae2')
      end
    end.
Proof.
  fold_unfold_tactic evaluate_m'.
Qed.

Lemma fold_unfold_evaluate_m'_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_m' (Minus ae1 ae2) =
    match evaluate_m' ae1 with
    | ae1' =>
      match evaluate_m' ae2 with
      | ae2' =>
        (Minus ae1' ae2')
      end
    end.
Proof.
  fold_unfold_tactic evaluate_m'.
Qed.


Theorem evaluate_m'_satisfies_the_specification_of_evaluate_m' :
  specification_of_evaluate_m' evaluate_m'.
Proof.
  unfold specification_of_evaluate_m'.
  split.
  - intro n.
    exact (fold_unfold_evaluate_m'_Literal n).
  - split.
    * intros ae1 ae2 ae1' ae2'.
      rewrite -> fold_unfold_evaluate_m'_Plus.
      intros H_ae1 H_ae2.
      rewrite -> H_ae1.
      rewrite -> H_ae2.
      reflexivity.
      * intros ae1 ae2 ae1' ae2'.
      rewrite -> fold_unfold_evaluate_m'_Minus.
      intros H_ae1 H_ae2.
      rewrite -> H_ae1.
      rewrite -> H_ae2.
      reflexivity.
Qed.

Definition specification_of_interpret_m' (interpret_m' : source_program -> source_program) :=
  forall evaluate_m' : arithmetic_expression -> arithmetic_expression,
    specification_of_evaluate_m' evaluate_m' ->
    forall ae : arithmetic_expression,
      interpret_m' (Source_program ae) = Source_program (evaluate_m' ae).


(* ********** *)

(* end of term-project.v *)
