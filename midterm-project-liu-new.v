(* midterm-project.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 20 Sep 2020 *)

(* ********** *)

(* A study of polymorphic lists. *)

(* name: Zhang Liu
   email address: zhangliu@u.yale-nus.edu.sg
   date: 9 October 2020

   please upload one .v file and one .pdf file containing a project report

   desiderata:
   - the file should be readable, i.e., properly indented and using items or {...} for subgoals
   - each use of a tactic should achieve one proof step
   - all lemmas should be applied to all their arguments
   - there should be no occurrences of admit, admitted, and abort
*)

(* ********** *)

(* Paraphernalia: *)
 
Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* ********** *)

Definition eqb_option (V : Type) (eqb_V : V -> V -> bool) (ov1 ov2 : option V) : bool :=
  match ov1 with
  | Some v1 =>
    match ov2 with
    | Some v2 =>
      eqb_V v1 v2
    | None =>
      false
    end
  | None =>
    match ov2 with
    | Some v2 =>
      false
    | None =>
      true
    end
  end.

Notation "A =on= B" :=
  (eqb_option nat beq_nat A B) (at level 70, right associativity).

Notation "A =ob= B" :=
  (eqb_option bool eqb A B) (at level 70, right associativity).

(* ********** *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
  end.

Lemma fold_unfold_eqb_list_nil :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v2s : list V),
    eqb_list V eqb_V nil v2s =
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

Lemma fold_unfold_eqb_list_cons :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v1 : V)
         (v1s' v2s : list V),
    eqb_list V eqb_V (v1 :: v1s') v2s =
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

(* -------------------------------------------------- *)
(* Exercise 0: Soundness and Completeness of the equality predicate for lists. *)
  
Theorem soundness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall v1s v2s : list V,
      eqb_list V eqb_V v1s v2s = true ->
      v1s = v2s.
 Proof.
  intros V eqb_V S_eqb_V v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - intros [ | v2 v2s'] H_eqb. 
    -- rewrite -> (fold_unfold_eqb_list_nil V eqb_V) in H_eqb.
       reflexivity.
    -- rewrite -> (fold_unfold_eqb_list_nil V eqb_V (v2 :: v2s')) in H_eqb.
       discriminate H_eqb. 
  - intros [ | v2 v2s'] H_eqb.
    -- rewrite -> (fold_unfold_eqb_list_cons V eqb_V) in H_eqb.
       discriminate H_eqb.
    -- rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' (v2 :: v2s')) in H_eqb.  
       Search (_ && _ = true).
       Check (andb_prop (eqb_V v1 v2) (eqb_list V eqb_V v1s' v2s') H_eqb).
       destruct (andb_prop (eqb_V v1 v2) (eqb_list V eqb_V v1s' v2s') H_eqb) as [H_eqb_1 H_eqb_2].
       rewrite -> (S_eqb_V v1 v2 H_eqb_1).
       rewrite -> (IHv1s' v2s' H_eqb_2).
       reflexivity.
Qed.

Theorem completeness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall v1s v2s : list V,
      v1s = v2s ->
      eqb_list V eqb_V v1s v2s = true.
Proof.
  intros V eqb_V C_eqb_V v1s.
  induction v1s as [ | v vs IHv1].
  - intros [ | v2 v2s'] H_eqb.
    -- rewrite -> (fold_unfold_eqb_list_nil V eqb_V nil).
       reflexivity.
    -- rewrite -> (fold_unfold_eqb_list_nil V eqb_V (v2 :: v2s')).
       discriminate.
  - intros [ | v2 v2s'].
    -- rewrite -> (fold_unfold_eqb_list_cons V eqb_V v vs).
       intro H_absurd.
       discriminate (H_absurd).
    -- rewrite -> (fold_unfold_eqb_list_cons V eqb_V v vs (v2 :: v2s')).
       intro H_eq.
       injection H_eq as H_eq_1 H_eq_2.
       Check (C_eqb_V v v2 H_eq_1).
       Check (IHv1 v2s' H_eq_2).
       rewrite -> (C_eqb_V v v2 H_eq_1).
       rewrite -> (IHv1 v2s' H_eq_2).
       unfold andb.
       reflexivity.
Qed.


(* ********** *)

(* A study of the polymorphic length function. *)

Definition specification_of_length (length : forall V : Type, list V -> nat) :=
  (forall V : Type,
      length V nil = 0)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
     length V (v :: vs') = S (length V vs')).

(* Unit-test function: *)

Definition test_length (candidate : forall V : Type, list V -> nat) :=
  (candidate nat nil =n= 0) &&
  (candidate bool nil =n= 0) &&
  (candidate nat (1 :: nil) =n= 1) &&
  (candidate bool (true :: nil) =n= 1) &&
  (candidate nat (2 :: 1 :: nil) =n= 2) &&
  (candidate bool (false :: true :: nil) =n= 2) &&
  (candidate nat (3 :: 2 :: 1 :: nil) =n= 3) &&
  (candidate bool (false :: false :: true :: nil) =n= 3) &&
  (candidate nat (5 :: 100 :: 1 :: 1 :: 2 :: 1 :: nil) =n= 6).

(* The specification specifies at most one length function: *)

Theorem there_is_at_most_one_length_function :
  forall (V : Type)
         (length_1 length_2 : forall V : Type, list V -> nat),
    specification_of_length length_1 ->
    specification_of_length length_2 ->
    forall vs : list V,
      length_1 V vs = length_2 V vs.
Proof.
  intros V length_1 length_2.
  unfold specification_of_length.
  intros [S_length_1_nil S_length_1_cons]
         [S_length_2_nil S_length_2_cons]
         vs.
  induction vs as [ | v vs' IHvs'].

  - Check (S_length_2_nil V).
    rewrite -> (S_length_2_nil V).
    Check (S_length_1_nil V).
    exact (S_length_1_nil V).

  - Check (S_length_1_cons V v vs').
    rewrite -> (S_length_1_cons V v vs').
    rewrite -> (S_length_2_cons V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(* The length function in direct style: *)

Fixpoint length_v0_aux (V : Type) (vs : list V) : nat :=
  match vs with
    | nil =>
      0
    | v :: vs' =>
      S (length_v0_aux V vs')
  end.

Definition length_v0 (V : Type) (vs : list V) : nat :=
  length_v0_aux V vs.

Compute (test_length length_v0).

(* Associated fold-unfold lemmas: *)

Lemma fold_unfold_length_v0_aux_nil :
  forall V : Type,
    length_v0_aux V nil =
    0.
Proof.
  fold_unfold_tactic length_v0_aux.
Qed.

Lemma fold_unfold_length_v0_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    length_v0_aux V (v :: vs') =
    S (length_v0_aux V vs').
Proof.
  fold_unfold_tactic length_v0_aux.
Qed.

(* The specification specifies at least one length function: *)

Theorem length_v0_satisfies_the_specification_of_length :
  specification_of_length length_v0.
Proof.
  unfold specification_of_length, length_v0.
  split.
  - exact fold_unfold_length_v0_aux_nil.
  - exact fold_unfold_length_v0_aux_cons.
Qed.

(* ***** *)

(* Exercise 1: Length Function *)

(* Implement the length function using an accumulator. *)

Fixpoint length_v1_aux (V : Type) (vs : list V) (a : nat): nat :=
  match vs with
    | nil =>
      a
    | v :: vs' =>
      length_v1_aux V vs' (S a)
  end.

Definition length_v1 (V : Type) (vs : list V) : nat :=
  length_v1_aux V vs 0.

Compute (test_length length_v1).

Lemma fold_unfold_length_v1_aux_nil :
  forall (V : Type)
         (a : nat),
    length_v1_aux V nil a =
    a.
Proof.
  fold_unfold_tactic length_v1_aux.
Qed.

Lemma fold_unfold_length_v1_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (a : nat),
    length_v1_aux V (v :: vs') a = length_v1_aux V vs' (S a).
Proof.
  fold_unfold_tactic length_v1_aux.
Qed.


Lemma length_v1_satisfies_the_specification_of_length_aux :
  forall (V : Type)
         (vs : list V)
         (a : nat),
    a + length_v1_aux V vs 0 = length_v1_aux V vs a.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  -  intro a.
     rewrite -> (fold_unfold_length_v1_aux_nil V a).
     rewrite -> (fold_unfold_length_v1_aux_nil V 0).
     Search (_ + 0).
     exact (Nat.add_0_r a).
  - intro a.
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs' a).
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs' 0).
    rewrite <- (IHvs' 1).
    Search (_ + (_ + _)).
    rewrite -> (Nat.add_assoc a 1 (length_v1_aux V vs' 0)).
    Search (_ + 1).
    rewrite -> (Nat.add_1_r a).
    rewrite -> (IHvs' (S a)).
    reflexivity.
Qed.


Theorem length_v1_satisfies_the_specification_of_length :
  specification_of_length length_v1.
Proof.
  unfold specification_of_length, length_v1.
  split.
  - intro V.
    exact (fold_unfold_length_v1_aux_nil V 0).
  - intros V v vs'.
    rewrite <- (Nat.add_1_l (length_v1_aux V vs' 0)).
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs' 0).
    rewrite <- (length_v1_satisfies_the_specification_of_length_aux V vs' 1).
    reflexivity.
Qed.

(* ********** *)


(* A study of the polymorphic, left-to-right indexing function: *)

(* ***** *)

(* The indexing function can be specified by induction over the given list: *)

Definition test_list_nth (candidate : forall V : Type, list V -> nat -> option V) :=
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 0) =on= (Some 0)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 1) =on= (Some 1)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 2) =on= (Some 2)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 3) =on= (Some 3)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 4) =on= None) &&
  ((candidate bool (true :: false :: nil) 5) =ob= None) &&
  ((candidate bool (true :: false :: true :: nil) 2) =ob= (Some true)) &&
  ((candidate bool (true :: false :: false :: nil) 2) =ob= (Some false)) &&
  ((candidate bool (true :: false :: false :: nil) 1) =ob= (Some false)) &&
  ((candidate bool (true :: false :: true :: nil) 0) =ob= (Some true)).

Fixpoint list_nth (V : Type) (vs : list V) (n : nat) : option V :=
  match vs with
  | nil =>
    None
  | v :: vs' =>
    match n with
    | O =>
      Some v
    | S n' =>
      list_nth V vs' n'
    end
  end.

Compute (test_list_nth list_nth).

Lemma fold_unfold_list_nth_nil :
  forall (V : Type)
         (n : nat),
    list_nth V nil n =
    None.
Proof.
  fold_unfold_tactic list_nth.
Qed.

Lemma fold_unfold_list_nth_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (n : nat),
    list_nth V (v :: vs') n =
    match n with
    | O =>
      Some v
    | S n' =>
      list_nth V vs' n'
    end.
Proof.
  fold_unfold_tactic list_nth.
Qed.

(* ***** *)

(* The indexing function can be specified by induction over the given index: *)
Definition test_nat_nth (candidate : forall V : Type, nat -> list V -> option V) :=
  ((candidate nat 0 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 0)) &&
  ((candidate nat 1 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 1)) &&
  ((candidate nat 2 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 2)) &&
  ((candidate nat 3 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 3)) &&
  ((candidate nat 4 (0 :: 1 :: 2 :: 3 :: nil)) =on= None) &&
  ((candidate nat 5 (0 :: 1 :: 2 :: 3 :: nil)) =on= None) &&
  ((candidate bool 0 (nil)) =ob= None) &&
  ((candidate bool 0 (true :: false :: true :: true :: nil)) =ob= (Some true)) &&
  ((candidate bool 2 (true :: false :: true :: true :: nil)) =ob= (Some true)) &&
  ((candidate bool 5 (true :: false :: true :: true :: nil)) =ob= None).

Fixpoint nat_nth (V : Type) (n : nat) (vs : list V) : option V :=
  match n with
  | O =>
    match vs with
    | nil =>
      None
    | v :: vs' =>
      Some v
    end
  | S n' =>
    match vs with
    | nil =>
      None
    | v :: vs' =>
      nat_nth V n' vs'
    end
  end.

Compute (test_nat_nth nat_nth).

Lemma fold_unfold_nat_nth_O :
  forall (V : Type)
         (vs : list V),
    nat_nth V O vs =
    match vs with
    | nil =>
      None
    | v :: vs' =>
      Some v
    end.
Proof.
  fold_unfold_tactic nat_nth.
Qed.

Lemma fold_unfold_nat_nth_S :
  forall (V : Type)
         (n' : nat)
         (vs : list V),
    nat_nth V (S n') vs =
    match vs with
    | nil =>
      None
    | v :: vs' =>
      nat_nth V n' vs'
    end.
Proof.
  fold_unfold_tactic nat_nth.
Qed.

(* ***** *)

(* Exercise 2: Indexing Function *)

(*
   a. Both list-indexing functions come with their own unit-test function.
      Test each implementation with the unit-test function of the other implementation,
      and verify that it passes this other test.
*)

Compute (test_list_nth (fun V vs n => nat_nth V n vs)).
Compute (test_nat_nth (fun V n vs => list_nth V vs n)).

(*
   b. prove that if, given a list and an index, list_nth yields a result,
      then given this index and this list, nat_nth yields the same result
*)

Proposition list_nth_implies_nat_nth :
  forall (V : Type)
         (vs : list V)
         (n : nat)
         (ov : option V),
    list_nth V vs n = ov ->
    nat_nth V n vs = ov.
Proof. 
  intros V vs n ov H_ov.
  revert vs H_ov.
  induction n as [ | n' IHn'].
  + intros [ | v vs'] H_ov.
  - rewrite -> (fold_unfold_nat_nth_O V nil).
    rewrite -> (fold_unfold_list_nth_nil V 0) in H_ov.
    exact H_ov.
  - rewrite -> (fold_unfold_nat_nth_O V (v :: vs')).
    rewrite -> (fold_unfold_list_nth_cons V v vs' 0) in H_ov.
    exact H_ov.
  + intros [ | v vs'] H_ov.
  - rewrite -> (fold_unfold_nat_nth_S V n' nil).
    rewrite -> (fold_unfold_list_nth_nil V (S n')) in H_ov.
    exact H_ov.
  - rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')).
    rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')) in H_ov.
    Check (IHn' vs').
    Check (IHn' vs' H_ov).
    exact (IHn' vs' H_ov).

  Restart.

  intros V vs.
  induction vs as [ | v vs' IHvs'].
  + intros [ | n'] ov H_ov.
  - rewrite -> (fold_unfold_nat_nth_O V nil).
    rewrite -> (fold_unfold_list_nth_nil V 0) in H_ov.
    exact H_ov.
  - rewrite -> (fold_unfold_nat_nth_S V n' nil).
    rewrite -> (fold_unfold_list_nth_nil V (S n')) in H_ov.
    exact H_ov.
  + intros [ | n'] ov H_ov.
  - rewrite -> (fold_unfold_nat_nth_O V (v :: vs')).
    rewrite -> (fold_unfold_list_nth_cons V v vs' 0) in H_ov.
    exact H_ov.
  - rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')).
    rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')) in H_ov.
    Check (IHvs' n').
    Check (IHvs' n' (list_nth V vs' n')).
    Check (eq_refl 3).
    Check (eq_refl (list_nth V vs' n')).
    Check (IHvs' n' (list_nth V vs' n') (eq_refl (list_nth V vs' n'))).
    rewrite -> (IHvs' n' (list_nth V vs' n') (eq_refl (list_nth V vs' n'))).
    exact (H_ov).
Qed.

(*
   c. prove that if, given an index and a list, nat_nth yields a result,
      then given this list and this index, list_nth yields the same result
*)

Proposition nat_nth_implies_list_nth :
  forall (V : Type)
         (n : nat)
         (vs : list V)
         (ov : option V),
    nat_nth V n vs = ov ->
    list_nth V vs n = ov.
Proof.
  intros V n.
  induction n as [ | n' IHn'].
  + intros [ | v vs'] ov H_ov.
  - rewrite -> (fold_unfold_list_nth_nil V 0).
    rewrite-> (fold_unfold_nat_nth_O V nil) in H_ov.
    exact H_ov.
  - rewrite -> (fold_unfold_list_nth_cons V v vs' 0).
    rewrite -> (fold_unfold_nat_nth_O V (v :: vs')) in H_ov.
    exact H_ov.
  + intros [ | v vs'] ov H_ov.
  - rewrite -> (fold_unfold_list_nth_nil V (S n')).
    rewrite -> (fold_unfold_nat_nth_S V n' nil) in H_ov.
    exact H_ov.
  - rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')).
    rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')) in H_ov.
    Check (IHn' vs' ov H_ov).
    exact (IHn' vs' ov H_ov).

  Restart.

  intros V n vs.
  revert n.
  induction vs as [ | v vs' IHvs'].
  + intros [ | n'] ov H_ov.
  - rewrite -> (fold_unfold_list_nth_nil V 0).
    rewrite -> (fold_unfold_nat_nth_O V nil) in H_ov.
    exact H_ov.
  - rewrite -> (fold_unfold_list_nth_nil V (S n')).
    rewrite -> (fold_unfold_nat_nth_S V n' nil) in H_ov.
    exact H_ov.
  + intros [ | n'] ov H_ov.
  - rewrite -> (fold_unfold_list_nth_cons V v vs' 0).
    rewrite -> (fold_unfold_nat_nth_O V (v :: vs'))  in H_ov.
    exact H_ov.
  - rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')).
    rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')) in H_ov.
    Check (IHvs' n' ov H_ov).
    exact (IHvs' n' ov H_ov).
Qed.

(*
   d. What do you conclude?
*)

Corollary list_nth_and_nat_nth_are_equivalent :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    list_nth V vs n = nat_nth V n vs.
Proof.
  intros V vs n.
  Check (list_nth_implies_nat_nth V vs n).
  Check (list_nth_implies_nat_nth V vs n (list_nth V vs n)).
  Check (list_nth_implies_nat_nth V vs n (list_nth V vs n) (eq_refl (list_nth V vs n))).
  symmetry.
  exact (list_nth_implies_nat_nth V vs n (list_nth V vs n) (eq_refl (list_nth V vs n))).

  Restart.

  intros V vs n.
  Check (nat_nth_implies_list_nth V n vs).
  Check (nat_nth_implies_list_nth V n vs (nat_nth V n vs)).
  Check (nat_nth_implies_list_nth V n vs (nat_nth V n vs) (eq_refl (nat_nth V n vs))).
  exact (nat_nth_implies_list_nth V n vs (nat_nth V n vs) (eq_refl (nat_nth V n vs))).
Qed.

(* ********** *)

(* A study of the polymorphic copy function: *)

Definition specification_of_copy (copy : forall V : Type, list V -> list V) :=
  (forall V : Type,
      copy V nil = nil)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
     copy V (v :: vs') = v :: (copy V vs')).

(* Exercise 3: Copy Function *)

(*   a. expand the unit-test function for copy with a few more tests *)

Definition test_copy (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat nil) nil) &&
  (eqb_list bool eqb (candidate bool nil) nil) &&
  (eqb_list nat beq_nat (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (2 :: 1 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (false :: true :: nil)) (false :: true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (3 :: 2 :: 1 :: nil)) (3 :: 2 :: 1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: false :: true :: nil)) (true :: false :: true :: nil)).

(*   b. implement the copy function in direct style *)

Fixpoint copy_v0_aux (V : Type) (vs : list V) : list V :=
  match vs with
  | nil =>
    nil
  | v :: vs' =>
    v :: (copy_v0_aux V vs')
  end.

Definition copy_v0 (V : Type) (vs : list V) : list V :=
  copy_v0_aux V vs.

Fixpoint copy_v2_aux (V: Type) (vs: list V) (a: list V) : list V :=
  match vs with
  | nil =>
    a
  | v :: vs' =>
    copy_v2_aux V vs' (v :: a)
  end.

(* How to implement this in direct style? *)

Definition copy_v2 (V: Type) (vs: list V): list V :=
 copy_v2_aux V (copy_v2_aux V vs nil) nil.

Compute (test_copy copy_v0).
Compute (test_copy copy_v2).

(*   c. state its associated fold-unfold lemmas *)

Lemma fold_unfold_copy_v0_aux_nil :
  forall (V : Type),
    copy_v0_aux V nil = nil.
Proof.
  fold_unfold_tactic copy_v0_aux.
Qed.

Lemma fold_unfold_copy_v0_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    copy_v0_aux V (v :: vs') = v :: copy_v0_aux V vs'.
Proof.
  fold_unfold_tactic copy_v0_aux.
Qed.

(*   d. prove whether your implementation satisfies the specification. *)

Theorem copy_v0_satisfies_its_specification :
  specification_of_copy copy_v0.
Proof.
  unfold specification_of_copy, copy_v0.
  split.
  - exact fold_unfold_copy_v0_aux_nil.
  - exact fold_unfold_copy_v0_aux_cons.
Qed.

(*   e. prove whether copy is idempotent *)

Proposition copy_is_idempotent :
  forall (V : Type)
         (vs : list V),
    copy_v0 V (copy_v0 V vs) = copy_v0 V vs.
Proof.
  intros V vs.
  unfold copy_v0.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_copy_v0_aux_nil V).
    rewrite -> (fold_unfold_copy_v0_aux_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_copy_v0_aux_cons V v vs').
    Check (fold_unfold_copy_v0_aux_cons V v (copy_v0 V vs')).
    rewrite -> (fold_unfold_copy_v0_aux_cons V v (copy_v0_aux V vs')).
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*   f. prove whether copying a list preserves its length *)

Proposition copy_preserves_length :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 V (copy_v0 V vs) = n.
Proof.
  intros V vs n.
  revert vs.
  unfold length_v0, copy_v0.
  induction n as [ | n' ].
  + intros [ | v vs' ] H_n.
  - rewrite -> (fold_unfold_copy_v0_aux_nil V).
    exact H_n.
  - rewrite -> (fold_unfold_length_v0_aux_cons V v vs') in H_n.
    discriminate H_n.
  + intros [ | v vs' ] H_n.
  - rewrite -> (fold_unfold_copy_v0_aux_nil V).
    exact H_n.
  - rewrite -> (fold_unfold_length_v0_aux_cons V v vs') in H_n.
    rewrite -> (fold_unfold_copy_v0_aux_cons V v vs').
    rewrite -> (fold_unfold_length_v0_aux_cons V v (copy_v0_aux V vs')).
    Search (S _ = S _).
    rewrite -> (eq_S (length_v0_aux V (copy_v0_aux V vs')) n').
    reflexivity.
    Check (IHn' vs' (eq_add_S (length_v0_aux V vs') n' H_n)).
    exact (IHn' vs' (eq_add_S (length_v0_aux V vs') n' H_n)).
Qed.

Proposition copy_preserves_length_alternative :
  forall (V : Type)
         (vs : list V),
    length_v0 V (copy_v0 V vs) = length_v0 V vs.
Proof.
  intros V vs.
  unfold length_v0, copy_v0.
  induction vs as [| v vs' IHvs'].
  + rewrite -> (fold_unfold_copy_v0_aux_nil V).
    reflexivity.
  + rewrite -> (fold_unfold_copy_v0_aux_cons V v vs').
    rewrite -> (fold_unfold_length_v0_aux_cons V v (copy_v0_aux V vs')).
    rewrite -> (fold_unfold_length_v0_aux_cons V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   g. subsidiary question: can you think of a strikingly simple implementation of the copy function?
      if so, pray show that it satisfies the specification of copy
 *)

Definition copy_v1 (V : Type) (vs : list V) : list V := vs.

Compute (test_copy copy_v1).

Theorem copy_v1_satisfies_its_specification :
  specification_of_copy copy_v1.
Proof.
  unfold specification_of_copy, copy_v1.
  split.
  - intro V.
    reflexivity.
  - intros V v vs'.
    reflexivity.
Qed.

(* ********** *)

(* A study of the polymorphic append function: *)

Definition specification_of_append (append : forall V : Type, list V -> list V -> list V) :=
  (forall (V : Type)
          (v2s : list V),
      append V nil v2s = v2s)
  /\
  (forall (V : Type)
          (v1 : V)
          (v1s' v2s : list V),
      append V (v1 :: v1s') v2s = v1 :: append V v1s' v2s).

(* ******* *)

(* Exercise 4: Append Function *)

(*  a. define a unit-test function for append *)

Definition test_append (candidate : forall V : Type, list V -> list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat nil nil) nil) &&
  (eqb_list bool eqb (candidate bool nil nil) nil) &&
  (eqb_list nat beq_nat (candidate nat nil (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool eqb (candidate bool nil (true :: nil)) (true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (2 :: nil) (1 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (false :: nil) (true :: nil)) (false :: true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (1 :: 2 :: nil) (3 :: 2 :: 1 :: nil)) (1 :: 2 :: 3 :: 2 :: 1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: false :: nil) (true :: nil)) (true :: false :: true :: nil)).

(* b. implement the append function in direct style *)

Fixpoint append_v0_aux (V : Type) (v1s v2s : list V) : list V :=
  match v1s with
  | nil =>
    v2s
  | v1 :: v1s' =>
    v1 :: append_v0_aux V v1s' v2s
  end.

Definition append_v0 (V : Type) (v1s v2s : list V) : list V :=
  append_v0_aux V v1s v2s.

Compute (test_append append_v0).

(* c. state its associated fold-unfold lemmas *)

Lemma fold_unfold_append_v0_aux_nil :
  forall (V : Type)
         (v2s : list V),
    append_v0_aux V nil v2s = v2s.
Proof.
  fold_unfold_tactic append_v0_aux.
Qed.

Lemma fold_unfold_append_v0_aux_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' : list V)
         (v2s : list V),
    append_v0_aux V (v1 :: v1s') v2s = v1 :: append_v0_aux V v1s' v2s.
Proof.
  fold_unfold_tactic append_v0_aux.
Qed.

(* d. prove that your implementation satisfies the specification *)

Theorem append_v0_satisfies_specification_of_append :
  specification_of_append append_v0.
Proof.
  unfold specification_of_append, append_v0.
  split.
  - intros V v2s.
    exact (fold_unfold_append_v0_aux_nil V v2s).
  - intros V v1 v1s' v2s.
    exact (fold_unfold_append_v0_aux_cons V v1 v1s' v2s).
Qed.

(*  e. prove whether nil is neutral on the left of append *)

Property nil_is_left_neutral_wrt_append :
  forall (V : Type)
         (v2s : list V),
    append_v0 V nil v2s = v2s.
Proof.
  intros V v2s.
  unfold append_v0.
  exact (fold_unfold_append_v0_aux_nil V v2s).
Qed.

(*   f. prove whether nil is neutral on the right of append *)

Lemma nil_is_right_neutral_wrt_append_aux :
  forall (V : Type)
         (v1s : list V),
    append_v0_aux V v1s nil = v1s.
Proof.
  intros V v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  + rewrite -> (fold_unfold_append_v0_aux_nil V nil).
    reflexivity.
  + rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s').
    rewrite -> IHv1s'.
    reflexivity.
Qed.

Property nil_is_right_neutral_wrt_append :
  forall (V : Type)
         (v1s : list V),
    append_v0 V v1s nil = v1s.
Proof.
  intros V v1s.
  unfold append_v0.
  exact (nil_is_right_neutral_wrt_append_aux V v1s).
Qed.

(*   g. prove whether append is commutative *)

Proposition append_is_not_commutative_for_lists_of_nat :
  exists v1s v2s : list nat, append_v0 nat v1s v2s <> append_v0 nat v2s v1s.
Proof.
  exists (1 :: nil).
  exists (2 :: nil).
  unfold not, append_v0.
  rewrite -> (fold_unfold_append_v0_aux_cons nat 1 nil (2 :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_cons nat 2 nil (1 :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_nil nat (2 :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_nil nat (1 :: nil)).
  intro H_tmp. 
  injection H_tmp as H_12 H_21.
  discriminate H_12.
Qed.

Proposition append_is_not_commutative :
  forall V : Type,
    (exists v1 v2 : V,
        v1 <> v2) ->
    exists v1s v2s : list V,
      append_v0 V v1s v2s <> append_v0 V v2s v1s.
Proof.
  unfold not, append_v0.
  intros V H.
  destruct H as [v1 [v2 H_v1v2]].
  exists (v1 :: nil).
  exists (v2 :: nil).
  rewrite -> (fold_unfold_append_v0_aux_cons V v1 nil (v2 :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_cons V v2 nil (v1 :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_nil V (v2 :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_nil V (v1 :: nil)).
  intro H_tmp.
  injection H_tmp as H_12 H_21.
  Check (H_v1v2 H_12).
  exact (H_v1v2 H_12).
  (* can also use contradiction (H_v1v2 H_12). *)
Qed.

(*   h. prove whether append is associative *)

Proposition append_is_associative :
  forall (V : Type)
         (v1s v2s v3s: list V),
    append_v0 V v1s (append_v0 V v2s v3s) = append_v0 V (append_v0 V v1s v2s) v3s.
Proof.
  intros V v1s.
  unfold append_v0.
  induction v1s as [ | v1 v1s' IHv1s'].
  + intros v2s v3s.
    rewrite -> (fold_unfold_append_v0_aux_nil V (append_v0_aux V v2s v3s)).
    rewrite -> (fold_unfold_append_v0_aux_nil V v2s).
    reflexivity.
  + intros v2s v3s.
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s' (append_v0_aux V v2s v3s)).
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 (append_v0_aux V v1s' v2s) v3s).
    rewrite -> (IHv1s' v2s v3s).
    reflexivity.
Qed.

Proposition append_aux_is_associative :
  forall (V : Type)
         (v1s v2s v3s: list V),
    append_v0_aux V v1s (append_v0_aux V v2s v3s) = append_v0_aux V (append_v0_aux V v1s v2s) v3s.
Proof.
  intros V v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  + intros v2s v3s.
    rewrite -> (fold_unfold_append_v0_aux_nil V (append_v0_aux V v2s v3s)).
    rewrite -> (fold_unfold_append_v0_aux_nil V v2s).
    reflexivity.
  + intros v2s v3s.
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s' (append_v0_aux V v2s v3s)).
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 (append_v0_aux V v1s' v2s) v3s).
    rewrite -> (IHv1s' v2s v3s).
    reflexivity.
Qed.

(*   i. prove whether appending two lists preserves their length *)

Proposition append_preserves_length :
  forall (V : Type)
         (v1s v2s : list V),
    length_v0 V (append_v0 V v1s v2s) = length_v0 V v1s + length_v0 V v2s.
Proof.
  intros V v1s.
  unfold append_v0, length_v0.
  induction v1s as [ | v1 v1s' IHv1s'].
  + intros v2s.
    rewrite -> (fold_unfold_append_v0_aux_nil V v2s).
    rewrite -> (fold_unfold_length_v0_aux_nil V).
    rewrite -> (Nat.add_comm 0 (length_v0_aux V v2s)).
    exact (plus_n_O (length_v0_aux V v2s)).
  + intros v2s.
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_length_v0_aux_cons V v1 (append_v0_aux V v1s' v2s)).
    rewrite -> (fold_unfold_length_v0_aux_cons V v1 v1s').
    rewrite -> (IHv1s' v2s).
    rewrite -> (plus_Sn_m (length_v0_aux V v1s') (length_v0_aux V v2s)).
    reflexivity.
Qed.

(* Xinyu's solution:
Proposition append_preserves_length_alt :
  forall (V : Type)
         (v1s v2s : list V)
         (n1 n2 : nat),
    length_v0 V v1s = n1 ->
    length_v0 V v2s = n2 ->
    length_v0 V (append_v0 V v1s v2s) = n1 + n2.
Proof.
  intros V v1s.
  unfold append_v0, length_v0.
  induction v1s as [ | v1 v1s' IHv1s'].
  + intros v2s n1 n2 H_n1 H_n2.
    rewrite -> (fold_unfold_append_v0_aux_nil V v2s).
    rewrite -> (fold_unfold_length_v0_aux_nil V) in H_n1.
    rewrite <- H_n1.
    rewrite -> (Nat.add_0_l n2).
    exact H_n2.
  + intros v2s n1 n2 H_n1 H_n2.
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_length_v0_aux_cons V v1 (append_v0_aux V v1s' v2s)).
    rewrite -> (fold_unfold_length_v0_aux_cons V v1 v1s') in H_n1. 
    case n1 as [ | n1'].
  - discriminate H_n1.
  - injection H_n1 as H_n1'.
    rewrite -> (IHv1s' v2s n1' n2 H_n1' H_n2).
    Search (S _ + _ = S (_ + _)).
    symmetry.
    exact (plus_Sn_m n1' n2).
Qed.
*)

(*
   j. prove whether append and copy commute with each other
*)

Proposition append_and_copy_v0_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    copy_v0 V (append_v0 V v1s v2s) = append_v0 V (copy_v0 V v1s) (copy_v0 V v2s).
Proof.
  intros V v1s.
  unfold append_v0, copy_v0.
  induction v1s as [| v1 v1s' IHv1s'].
  + intro v2s.
    rewrite -> (fold_unfold_append_v0_aux_nil V v2s).
    rewrite -> (fold_unfold_copy_v0_aux_nil V).
    rewrite -> (fold_unfold_append_v0_aux_nil V (copy_v0_aux V v2s)).
    reflexivity.
  + intro v2s.
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_copy_v0_aux_cons V v1 (append_v0_aux V v1s' v2s)).
    rewrite -> (fold_unfold_copy_v0_aux_cons V v1 v1s').
    rewrite -> (fold_unfold_append_v0_aux_cons V v1 (copy_v0_aux V v1s') (copy_v0_aux V v2s)).
    rewrite -> (IHv1s' v2s).
    reflexivity.
Qed.

Proposition append_and_copy_v1_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    copy_v1 V (append_v0 V v1s v2s) = append_v0 V (copy_v1 V v1s) (copy_v1 V v2s).
Proof.
  intros V v1s v2s.
  unfold append_v0, copy_v1.
  reflexivity.
Qed.

(* ********** *)


(* A study of the polymorphic reverse function: *)

Definition specification_of_reverse (reverse : forall V : Type, list V -> list V) :=
  forall append : forall W : Type, list W -> list W -> list W,
    specification_of_append append ->
    (forall V : Type,
        reverse V nil = nil)
    /\
    (forall (V : Type)
            (v : V)
            (vs' : list V),
        reverse V (v :: vs') = append V (reverse V vs') (v :: nil)).

(* Exercise 5: Reverse Function *)

(*
   a. define a unit-test function for reverse
 *)

Definition test_reverse (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat nil) nil) &&
  (eqb_list bool eqb (candidate bool nil) nil) &&
  (eqb_list nat beq_nat (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (2 :: 1 :: nil)) (1 :: 2 :: nil)) &&
  (eqb_list bool eqb (candidate bool (false :: true :: nil)) (true :: false :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (3 :: 2 :: 1 :: nil)) (1 :: 2 :: 3 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: false :: true :: nil)) (true :: false :: true :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: true :: true :: false :: true :: nil)) (true :: false :: true :: true :: true :: nil)) &&
  (eqb_list bool eqb (candidate bool (false :: true :: true :: false :: true :: nil)) (true :: false :: true :: true :: false :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (5 :: 7 :: 2 :: 1 :: nil)) (1 :: 2 :: 7 :: 5 :: nil)).

(* b. implement the reverse function in direct style, using append *)

Fixpoint reverse_v0_aux (V : Type) (vs : list V) : list V :=
  match vs with
  | nil =>
    nil
  | v :: vs' =>
    append_v0 V (reverse_v0_aux V vs') (v :: nil)
  end.

Definition reverse_v0 (V : Type) (vs : list V) : list V :=
  reverse_v0_aux V vs.

Compute (test_reverse reverse_v0).


(* c. state the associated fold-unfold lemmas *)

Lemma fold_unfold_reverse_v0_aux_nil :
  forall (V : Type),
    reverse_v0_aux V nil = nil.
Proof.
  fold_unfold_tactic reverse_v0_aux.
Qed.

Lemma fold_unfold_reverse_v0_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    reverse_v0_aux V (v :: vs') = append_v0 V (reverse_v0_aux V vs') (v :: nil).
Proof.
  fold_unfold_tactic reverse_v0_aux.
Qed.

(* d. prove that your implementation satisfies the specification *)

Proposition there_is_at_most_one_function_satisfying_the_specification_of_append :
  forall (append1 append2 : forall V : Type, list V -> list V -> list V),
    specification_of_append append1 ->
    specification_of_append append2 ->
    forall (V : Type)
           (v1s : list V)
           (v2s : list V),
      append1 V v1s v2s = append2 V v1s v2s.
Proof.
  intros append1 append2.
  unfold specification_of_append.
  intros [S1_nil S1_cons] [S2_nil S2_cons] V v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - intro v2s.
    rewrite -> (S1_nil V v2s).
    rewrite -> (S2_nil V v2s).
    reflexivity.
  - intro v2s.
    rewrite -> (S1_cons V v1 v1s' v2s).
    rewrite -> (S2_cons V v1 v1s' v2s).
    rewrite -> (IHv1s' v2s).
    reflexivity.
Qed.

Theorem reverse_satisfies_specification_of_reverse :
  specification_of_reverse reverse_v0.
Proof.
  unfold specification_of_reverse, reverse_v0.
  intros append S_append.
  split.
  - exact fold_unfold_reverse_v0_aux_nil.
  - intros V v vs'.
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v vs'). 
    rewrite -> (there_is_at_most_one_function_satisfying_the_specification_of_append append_v0 append).
    reflexivity.
    exact (append_v0_satisfies_specification_of_append).
    exact (S_append).
Qed.


(* e. prove whether reverse is involutory *)

(* testing in intro to CS, proving in FPP *)
(* prove the nil version yes, second part is corollary *) 

Lemma reverse_is_involutory_aux :
  forall (V : Type)
         (vs : list V)
         (v : V),
    reverse_v0_aux V (append_v0_aux V vs (v :: nil)) = append_v0_aux V (reverse_v0_aux V (v :: nil)) (reverse_v0_aux V vs).
Proof. 
  intros V vs v.
  rewrite -> (fold_unfold_reverse_v0_aux_cons V v nil).
  rewrite -> (fold_unfold_reverse_v0_aux_nil V).
  rewrite -> (nil_is_left_neutral_wrt_append V (v :: nil)).
  rewrite -> (fold_unfold_append_v0_aux_cons V v nil (reverse_v0_aux V vs)).
  rewrite -> (fold_unfold_append_v0_aux_nil V).
  induction vs as [ | v' vs' IHvs'].
  - rewrite -> (fold_unfold_append_v0_aux_nil V).
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v nil).
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_append_v0_aux_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_append_v0_aux_cons V v' vs' (v :: nil)).
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v' vs').
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v' (append_v0_aux V vs' (v :: nil))).
    rewrite -> (IHvs').
    unfold append_v0.
    rewrite <- (fold_unfold_append_v0_aux_cons V v (reverse_v0_aux V vs') (v' :: nil)).
    reflexivity.
Qed.

Lemma reverse_is_involutory_aux' :
  forall (V : Type)
         (vs : list V)
         (v : V),
    reverse_v0_aux V (append_v0_aux V vs (v :: nil)) = v :: reverse_v0_aux V vs.
Proof.
  intros V vs v.
  induction vs as [ | v' vs' IHvs'].
  - rewrite -> (fold_unfold_append_v0_aux_nil V).
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v nil). 
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_append_v0_aux_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_append_v0_aux_cons V v' vs' (v :: nil)).
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v' vs').
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v' (append_v0_aux V vs' (v :: nil))).
    rewrite -> (IHvs').
    unfold append_v0.
    rewrite <- (fold_unfold_append_v0_aux_cons V v (reverse_v0_aux V vs') (v' :: nil)).
    reflexivity.
Qed.
  

Proposition reverse_is_involutory :
  forall (V : Type)
         (vs : list V),
    reverse_v0 V (reverse_v0 V vs) = vs.
Proof.
  intros V.
  unfold reverse_v0.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v0_aux_cons V v vs').
    unfold append_v0.
    rewrite -> (reverse_is_involutory_aux' V (reverse_v0_aux V vs') v).
    rewrite -> (IHvs').
    reflexivity.
Qed.           

(* f. prove whether reversing a list preserves its length *)

Proposition reverse_preserves_length :
  forall (V : Type)
         (vs : list V),
    length_v0 V (reverse_v0 V vs) = length_v0 V vs.
Proof.
  intros V vs.
  unfold reverse_v0.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v0_aux_cons V v vs').
    rewrite -> (append_preserves_length V (reverse_v0_aux V vs') (v :: nil)).
    rewrite -> IHvs'.
    unfold length_v0.
    rewrite -> (fold_unfold_length_v0_aux_cons V v nil).
    rewrite -> (fold_unfold_length_v0_aux_nil V).
    rewrite -> (fold_unfold_length_v0_aux_cons V v vs').
    Search (_ + 1).
    rewrite -> (Nat.add_1_r (length_v0_aux V vs')).
    reflexivity.
Qed.

(* g. do append and reverse commute with each other (hint: yes they do) and if so how? *)

Lemma append_v0_aux_and_reverse_v0_aux_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    reverse_v0_aux V (append_v0_aux V v1s v2s) =
    append_v0_aux V (reverse_v0_aux V v2s) (reverse_v0_aux V v1s).
Proof. 
  intros V v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - intros [ | v2 v2s'].  
    (* equivalent to destruct v2s as [ | v2 v2s']. *)
     + unfold append_v0.
      rewrite -> (fold_unfold_append_v0_aux_nil V).
      rewrite -> (fold_unfold_reverse_v0_aux_nil V).
      rewrite -> (fold_unfold_append_v0_aux_nil V).
      reflexivity.
     + rewrite -> (fold_unfold_reverse_v0_aux_nil V).
       rewrite -> (fold_unfold_append_v0_aux_nil V (v2 :: v2s')). 
       rewrite -> (nil_is_right_neutral_wrt_append_aux V (reverse_v0_aux V (v2 :: v2s'))).
       reflexivity.
  - intros [ | v2 v2s']. 
    + rewrite -> (nil_is_right_neutral_wrt_append_aux V (v1 :: v1s')).
      rewrite -> (fold_unfold_reverse_v0_aux_nil V).
      rewrite -> (fold_unfold_append_v0_aux_nil V (reverse_v0_aux V (v1 :: v1s'))).
      reflexivity. 
    + unfold append_v0.
      unfold append_v0 in IHv1s'.
      rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s').
      rewrite -> (fold_unfold_reverse_v0_aux_cons V v2 v2s').
      unfold append_v0.
      rewrite -> (fold_unfold_reverse_v0_aux_cons V v1 v1s').
      rewrite -> (fold_unfold_reverse_v0_aux_cons V v1 (append_v0_aux V v1s' (v2 :: v2s'))).
      rewrite -> (IHv1s' (v2 :: v2s')).
      rewrite -> (fold_unfold_reverse_v0_aux_cons V v2 v2s').
      unfold append_v0.
      rewrite -> (append_aux_is_associative V (append_v0_aux V (reverse_v0_aux V v2s') (v2 :: nil)) (reverse_v0_aux V v1s') (v1 :: nil)).
      reflexivity.
Qed.
(*
rewrite -> (fold_unfold_append_v0_aux_cons V v1 v1s').
      rewrite -> (fold_unfold_reverse_v0_aux_cons V v2 v2s').
      unfold append_v0.
      rewrite -> (fold_unfold_reverse_v0_aux_cons V v1 v1s').
      unfold append_v0.
      rewrite -> (fold_unfold_reverse_v0_aux_cons V v1 (append_v0_aux V v1s' (v2 :: v2s'))).
      rewrite -> (IHv1s' (v2 :: v2s')).
      rewrite -> (fold_unfold_reverse_v0_aux_cons V v2 v2s').
      unfold append_v0.
      rewrite -> (append_aux_is_associative V (append_v0_aux V (reverse_v0_aux V v2s') (v2 :: nil)) (reverse_v0_aux V v1s') (v1 :: nil)).
      reflexivity.
 *)


Theorem append_and_reverse_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    reverse_v0 V (append_v0 V v1s v2s) =
    append_v0 V (reverse_v0 V v2s) (reverse_v0 V v1s).
Proof. 
  intros V v1s v2s.
  unfold reverse_v0, append_v0.
  exact (append_v0_aux_and_reverse_v0_aux_commute_with_each_other V v1s v2s).
Qed.  


(* h. implement the reverse function using an accumulator instead of using append *)

(*
Theorem reverse_v1_satisfies_specification_of_reverse : 
  specification_of_reverse reverse_v1.
Proof. 
  unfold specification_of_reverse, reverse_v1.
  intros append S_append.
  split.
  - intro V.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V nil).
    reflexivity.
  - intros V v vs'.
    rewrite <- (there_is_at_most_one_function_satisfying_the_specification_of_append append_v0 append). 
    rewrite <- (fold_unfold_reverse_v1_aux_nil V vs').
    Check  (fold_unfold_reverse_v1_aux_cons).
   Check (fold_unfold_append_v0_aux_cons).  
    admit. 
    exact (append_v0_satisfies_specification_of_append).
    exact (S_append).
*)


Fixpoint reverse_v1_aux (V : Type) (vs : list V) (a : list V) : list V :=
  match vs with
  | nil =>
    a
  | v :: vs' =>
    reverse_v1_aux V vs' (v :: a)
  end.

Definition reverse_v1 (V : Type) (vs : list V) : list V :=
  reverse_v1_aux V vs nil.

Compute (test_reverse reverse_v1).


Lemma fold_unfold_reverse_v1_aux_nil :
  forall (V : Type)
         (a : list V),
    reverse_v1_aux V nil a = a.
Proof.
  fold_unfold_tactic reverse_v1_aux.
Qed.

Lemma fold_unfold_reverse_v1_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (a : list V),
    reverse_v1_aux V (v :: vs') a = reverse_v1_aux V vs' (v :: a).
Proof.
  fold_unfold_tactic reverse_v1_aux.
Qed.


Lemma about_reverse_v1_aux :
    forall (V : Type)
         (vs a : list V),
      reverse_v1_aux V vs a = append_v0_aux V (reverse_v1_aux V vs nil) a.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - intro a.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V a).
    rewrite -> (fold_unfold_reverse_v1_aux_nil V nil).
    rewrite -> (fold_unfold_append_v0_aux_nil V).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs').
    rewrite -> (IHvs' (v :: a)).
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs').
    rewrite -> (IHvs' (v :: nil)).
    rewrite <- (append_aux_is_associative V (reverse_v1_aux V vs' nil) (v :: nil) a).
    rewrite -> (fold_unfold_append_v0_aux_cons V v nil).
    rewrite -> (fold_unfold_append_v0_aux_nil V a).
    reflexivity.
Qed.
    
Theorem reverse_v1_satisfies_specification_of_reverse : 
  specification_of_reverse reverse_v1.
Proof.
  unfold specification_of_reverse, reverse_v1.
  intros append S_append.
  split.
  - intro V.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V nil).
    reflexivity.
  - intros V v vs'.
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' nil).
    rewrite -> (about_reverse_v1_aux V vs'(v :: nil)).
    rewrite -> (there_is_at_most_one_function_satisfying_the_specification_of_append append_v0_aux append).
    reflexivity.
    exact (append_v0_satisfies_specification_of_append).
    exact S_append.
Qed.

(* i. revisit the propositions above (involution, preservation of length, commutation with append) and prove whether your implementation using an accumulator satisfies them *)

Theorem reverse_v0_and_reverse_v1_are_equivalent :
  forall (V : Type)
         (vs : list V),
    reverse_v0 V vs = reverse_v1 V vs.
Proof.
  intros V vs.
  unfold reverse_v0, reverse_v1.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v1_aux_nil V nil).
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v0_aux_cons V v vs').
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' nil).
    rewrite -> (IHvs').
    unfold append_v0.
    rewrite -> (about_reverse_v1_aux V vs' (v :: nil)).
    reflexivity.
Qed.

Proposition reverse_v1_is_involutory :
  forall (V : Type)
         (vs : list V),
    reverse_v1 V (reverse_v1 V vs) = vs.
Proof.
  intros V vs.
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V vs).
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V (reverse_v0 V vs)).
  exact (reverse_is_involutory V vs).
Qed.

Proposition reverse_v1_preserves_length :
  forall (V : Type)
         (vs : list V),
    length_v0 V (reverse_v1 V vs) = length_v0 V vs.
Proof.
  intros V vs.
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V vs).
  exact (reverse_preserves_length V vs).
Qed.

Theorem append_and_reverse_v1_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    reverse_v1 V (append_v0 V v1s v2s) = append_v0 V (reverse_v1 V v2s) (reverse_v1 V v1s).
Proof.
  intros V v1s v2s.
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V v1s).
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V v2s).
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V (append_v0 V v1s v2s)).
  exact (append_and_reverse_commute_with_each_other V v1s v2s).
Qed.
 


(* ********** *)

(* A study of the polymorphic map function: *)

Definition specification_of_map (map : forall V W : Type, (V -> W) -> list V -> list W) :=
  (forall (V W : Type)
          (f : V -> W),
      map V W f nil = nil)
  /\
  (forall (V W : Type)
          (f : V -> W)
          (v : V)
          (vs' : list V),
      map V W f (v :: vs') = f v :: map V W f vs').

(* Exercise 6:

   a. prove whether the specification specifies at most one map function

   b. implement the map function in direct style

   c. state its associated fold-unfold lemmas

   d. prove whether your implementation satisfies the specification

   e. implement the copy function using map

   f. prove whether mapping a function over a list preserves the length of this list

   g. do map and append commute with each other and if so how?

   h. do map and reverse commute with each other and if so how?

   i. define a unit-test function for map and verify that your implementation satisfies it
*)

(* ********** *)

(* A study of the polymorphic fold-right and fold-left functions: *)

Definition specification_of_list_fold_right (list_fold_right : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     list_fold_right V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     list_fold_right V W nil_case cons_case (v :: vs') =
     cons_case v (list_fold_right V W nil_case cons_case vs')).

Definition specification_of_list_fold_left (list_fold_left : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     list_fold_left V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     list_fold_left V W nil_case cons_case (v :: vs') =
     list_fold_left V W (cons_case v nil_case) cons_case vs').

(* Exercise 7: Fold-right and Fold-left Functions *)

(*
   a. implement the fold-right function in direct style
*)

Fixpoint list_fold_right_aux (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    cons_case v (list_fold_right_aux V W nil_case cons_case vs')
  end.

Definition list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  list_fold_right_aux V W nil_case cons_case vs.

(*
   b. implement the fold-left function in direct style
*)

Fixpoint list_fold_left_aux (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    list_fold_left_aux V W (cons_case v nil_case) cons_case vs'
  end.

Definition list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  list_fold_left_aux V W nil_case cons_case vs.

(*
   c. state the fold-unfold lemmas associated to list_fold_right and to list_fold_left
 *)

Lemma fold_unfold_list_fold_right_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_right V W nil_case cons_case nil = nil_case.
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_right_cons :
    forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_right V W nil_case cons_case (v :: vs') = cons_case v (list_fold_right V W nil_case cons_case vs').
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_left_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_left V W nil_case cons_case nil = nil_case.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

Lemma fold_unfold_list_fold_left_cons :
    forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_left V W nil_case cons_case (v :: vs') = list_fold_left V W (cons_case v nil_case) cons_case vs'.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

Definition is_left_permutative (V W : Type) (op2 : V -> W -> W) :=
  forall (v1 v2 : V)
         (v3 : W),
    op2 v1 (op2 v2 v3) = op2 v2 (op2 v1 v3).

Lemma finale_eureka :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    is_left_permutative V W cons_case ->
    forall (nil_case : W)
           (v : V)
           (vs : list V),
    list_fold_left V W (cons_case v nil_case) cons_case vs =
    cons_case v (list_fold_left V W nil_case cons_case vs).
Proof.
  intros V W cons_case.
  intro H_leftp.
  unfold is_left_permutative in H_leftp.
  intros nil_case v.
  intro vs.
  revert nil_case.
  induction vs as [ | v' vs' IHvs'].
  - intro nil_case.
    Check (fold_unfold_list_fold_left_nil V W (cons_case v nil_case) cons_case).
    rewrite ->  (fold_unfold_list_fold_left_nil V W (cons_case v nil_case) cons_case).
    rewrite ->  (fold_unfold_list_fold_left_nil V W nil_case cons_case).
    reflexivity.
  - intro nil_case.
    rewrite -> (fold_unfold_list_fold_left_cons V W (cons_case v nil_case) cons_case v' vs').
    rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v' vs').
    Check (IHvs' (cons_case v' nil_case)).
    Check (H_leftp v' v nil_case).
    rewrite -> (H_leftp v' v nil_case).
    exact (IHvs' (cons_case v' nil_case)).
Qed.


(*
   d. prove that each of your implementations satisfies the corresponding specification
 *)

Theorem list_fold_right_satisfies_the_specification_of_list_fold_right :
  specification_of_list_fold_right list_fold_right.
Proof.
  unfold specification_of_list_fold_right.
  split.
  - exact (fold_unfold_list_fold_right_nil).
  - exact (fold_unfold_list_fold_right_cons).
Qed.

Theorem list_fold_left_satisfies_the_specification_of_list_fold_left :
  specification_of_list_fold_left list_fold_left.
Proof.
  unfold specification_of_list_fold_left.
  split.
  - exact (fold_unfold_list_fold_left_nil).
  - exact (fold_unfold_list_fold_left_cons).
Qed.

(*
   e. which function do foo and bar (defined just below) compute?
*)

Definition foo (V : Type) (vs : list V) :=
  list_fold_right V (list V) nil (fun v vs => v :: vs) vs.

Compute (foo nat (2 :: 1 :: nil)).

Compute (test_copy foo).

Theorem foo_is_equivalent_to_copy :
   forall (V : Type)
         (vs : list V),
  foo V vs = copy_v1 V vs.
Proof.
  unfold foo, copy_v1.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_list_fold_right_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
    reflexivity.
  - rewrite -> (fold_unfold_list_fold_right_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(* foo is a copy function for polymorphic lists *)

Definition bar (V : Type) (vs : list V) :=
  list_fold_left V (list V) nil (fun v vs => v :: vs) vs.

Compute (bar nat (2 :: 1 :: nil)).

Compute (test_reverse bar).

Lemma about_list_fold_left_for_lists :
    forall (V : Type)
           (vs a : list V),
       list_fold_left V (list V) a (fun (v : V) (vs' : list V) => v :: vs') vs =
       append_v0_aux V (list_fold_left V (list V) nil (fun (v : V) (vs' : list V) => v :: vs') vs) a.
Proof.
    unfold append_v0.
    intros V vs.
    induction vs as [ | v' vs' IHvs'].
    - intro a.
      rewrite -> (fold_unfold_list_fold_left_nil V (list V) a (fun v vs' => v :: vs')).
      rewrite -> (fold_unfold_list_fold_left_nil V (list V) nil (fun v vs' => v :: vs')).
      rewrite -> (fold_unfold_append_v0_aux_nil V a).
      reflexivity.
      
    - intro a.
      rewrite -> (fold_unfold_list_fold_left_cons V (list V) a (fun v vs' => v :: vs') v' vs'). 
      rewrite -> (fold_unfold_list_fold_left_cons V (list V) nil (fun v vs' => v :: vs') v' vs').
      rewrite -> (IHvs' (v' :: a)).
      rewrite -> (IHvs' (v' :: nil)).
      rewrite <- (append_aux_is_associative
                    V
                    (list_fold_left V (list V) nil (fun (v0 : V) (vs'0 : list V) => v0 :: vs'0) vs')
                    (v' :: nil)
                    a).
      rewrite -> (fold_unfold_append_v0_aux_cons V v' nil a).
      rewrite -> (fold_unfold_append_v0_aux_nil V a).
      reflexivity.
Qed.


Theorem bar_is_equivalent_to_reverse :
  forall (V : Type)
         (vs : list V),
  bar V vs = reverse_v1 V vs.
Proof.
  unfold bar, reverse_v1.
  intros V vs.
  induction vs as [ | v' vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v1_aux_nil V nil).
    rewrite -> (fold_unfold_list_fold_left_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v1_aux_cons V v' vs' nil).
    rewrite -> (fold_unfold_list_fold_left_cons V (list V) nil (fun (v : V) (vs : list V) => v :: vs) v' vs'). 
    rewrite -> (about_reverse_v1_aux V vs' (v' :: nil)).
    rewrite <- IHvs'. 
    Check (about_list_fold_left_for_lists V vs' (v' :: nil)).
    apply (about_list_fold_left_for_lists V vs' (v' :: nil)).
Qed.
    
(* bar is a reverse function for polymorphic lists *)


(* f. implement length using either list_fold_right or list_fold_left, and justify your choice *)

Definition length_fold_left (V : Type) (vs : list V) : nat :=
  list_fold_left V nat 0 (fun v l => S l) vs.

Compute (test_length length_fold_left).

(* fold left is tail recursive *)

Lemma S_is_left_permutative :
  forall (V: Type),
    forall (n : nat),
    is_left_permutative V nat (fun _ n => S n).
Proof.
  unfold is_left_permutative.
  intro n.
  reflexivity.  
Qed.            

Theorem length_fold_left_satisfies_the_specification_of_length :
  specification_of_length length_fold_left.
Proof.
  unfold specification_of_length, length_fold_left.
  split.
  - intro V.
    exact (fold_unfold_list_fold_left_nil V nat 0 (fun (_ : V) (l : nat) => S l)).
  - intros V v vs'. 
    rewrite -> (fold_unfold_list_fold_left_cons V nat 0 (fun (_ : V) (l : nat) => S l) v vs').  
    Check (finale_eureka V nat (fun (_ : V) (l : nat) => S l)).
    assert (H_finale := finale_eureka V nat (fun (_ : V) (l : nat) => S l)).
    rewrite -> (H_finale).
    reflexivity.
    Check (S_is_left_permutative V).
    assert (H_S := S_is_left_permutative V 0).
    apply H_S. 
    apply v.
Qed.


(*
   g. implement copy using either list_fold_right or list_fold_left, and justify your choice
*)

Definition copy_fold_right (V : Type) (vs : list V) :=
  list_fold_right V (list V) nil (fun v vs => v :: vs) vs.

Compute (test_copy copy_fold_right).

Theorem copy_fold_right_satisfies_its_specification :
  specification_of_copy copy_fold_right.
Proof.
  unfold specification_of_copy, copy_fold_right.
  split.
  - intro V.
    reflexivity.
  - intros V v vs'.
    reflexivity.
Qed.

(*
   h. implement append using either list_fold_right or list_fold_left, and justify your choice *)

Definition append_fold_right (V : Type) (v1s v2s : list V) : list V :=
  list_fold_right V (list V) v2s (fun v1 v1s' => v1 :: v1s') v1s.

Compute (test_append append_fold_right).


Lemma fold_unfold_append_fold_right_aux_nil :
  forall (V : Type)
         (v2s : list V),
    append_fold_right V nil v2s = v2s.
Proof.
  fold_unfold_tactic append_fold_right.
Qed.

Lemma fold_unfold_append_fold_right_aux_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' : list V)
         (v2s : list V),
    append_fold_right V (v1 :: v1s') v2s = v1 :: append_fold_right V v1s' v2s.
Proof.
  fold_unfold_tactic append_fold_right.
Qed.


Theorem append_fold_right_satisfies_specification_of_append :
  specification_of_append append_fold_right.
Proof.
  unfold specification_of_append, append_fold_right.
  split.
  - intros V v2s.
    exact (fold_unfold_append_fold_right_aux_nil V v2s).
  - intros V v1 v1s' v2s.
    exact (fold_unfold_append_fold_right_aux_cons V v1 v1s' v2s).
Qed.


(*i. implement reverse using either list_fold_right or list_fold_left, and justify your choice *)

Definition reverse_fold_left (V : Type) (vs : list V) :=
  list_fold_left V (list V) nil (fun v vs => v :: vs) vs.


Compute (test_reverse reverse_fold_left).

(* fold left is tail recursive *)

(* 
compare with an earlier version: 
forall (V : Type)
         (v : V)
         (vs: list V),
     list_fold_left V (list V) (v :: nil)
       (fun (v : V) (vs' : list V) => v :: vs') vs =
     append_v0 V
              (list_fold_left V
                              (list V)
                              nil
                              (fun (v : V) (vs' : list V) => v :: vs') vs)
              (v :: nil).
*)
Theorem reverse_fold_left_satisfies_the_specification_of_reverse :
  specification_of_reverse reverse_fold_left.
Proof.
  unfold specification_of_reverse, reverse_fold_left.
  split. 
  - intro V.
    exact (fold_unfold_list_fold_left_nil V (list V) nil  (fun (v : V) (vs : list V) => v :: vs)).
  - intros V v vs'. 
    rewrite -> (fold_unfold_list_fold_left_cons V (list V) nil (fun (v : V) (vs : list V) => v :: vs) v vs').
    Check (there_is_at_most_one_function_satisfying_the_specification_of_append).
    Check (there_is_at_most_one_function_satisfying_the_specification_of_append
             append_v0
             append
             append_v0_satisfies_specification_of_append
             H
             V
             (list_fold_left V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs')
             (v :: nil)
          ). 
    rewrite <- (there_is_at_most_one_function_satisfying_the_specification_of_append
                  append_v0
                  append
                  append_v0_satisfies_specification_of_append
                  H
                  V
                  (list_fold_left V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) vs')
                  (v :: nil)
               ).      
    Check (about_list_fold_left_for_lists V vs' (v :: nil)).
    apply (about_list_fold_left_for_lists V vs' (v :: nil)).
Qed.

(*
[optional]  j. implement map using either list_fold_right or list_fold_left, and justify your choice
*)


(*k. relate list_fold_right and list_fold_left using reverse
Outline:
  for all vs, 
  LFL (rev (vs)) = LFR (vs)
  LFR (rev (vs)) = LFL (vs)
  use reverse_is_involutory.
*)
 
Lemma about_list_fold_left_and_append_v0_aux :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v1s v2s : list V),
    list_fold_left V W
                   nil_case
                   cons_case
                   (append_v0_aux V v1s v2s) =
    list_fold_left V W
                   (list_fold_left V W nil_case cons_case v1s)
                   cons_case
                   v2s.
Proof. (* by induction using the Light of Inductil *)
    intros V W nil_case cons_case v1s v2s.
   revert nil_case.
   induction v1s as [ | v1' v1s' IHv1s'].
    - intro nil_case.
     rewrite -> (fold_unfold_append_v0_aux_nil V).
     rewrite -> (fold_unfold_list_fold_left_nil V).
     reflexivity.
    - intro nil_case.
      Check (about_list_fold_left_for_lists).  
      rewrite -> (fold_unfold_append_v0_aux_cons V v1' v1s').   
      rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v1' v1s').
      rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v1' (append_v0_aux V v1s' v2s)).
      rewrite -> (IHv1s'  (cons_case v1' nil_case) ).
      reflexivity.
Qed. 

Lemma about_list_fold_left_and_reverse_v0_aux :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs : list V),
    list_fold_left V W nil_case cons_case (reverse_v0_aux V (v :: vs)) =
    cons_case v (list_fold_left V W nil_case cons_case (reverse_v0_aux V vs)).
Proof.
  intros V W nil_case cons_case v vs.
  revert v nil_case. (* behold the Light of Inductil *)
  induction vs as [ | v' vs' IHvs'].
  - intros v nil_case.
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v nil).
    unfold append_v0.
    rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_append_v0_aux_nil V (v :: nil)). 
    rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v nil).  
    rewrite -> (fold_unfold_list_fold_left_nil V W (cons_case v nil_case) cons_case).
    rewrite -> (fold_unfold_list_fold_left_nil V W nil_case cons_case).
   reflexivity.
  - intros v nil_case.
    rewrite -> (fold_unfold_reverse_v0_aux_cons V v (v' :: vs')).
    unfold append_v0.
    Check (append_v0_aux_and_reverse_v0_aux_commute_with_each_other).
    Check (append_v0_aux_and_reverse_v0_aux_commute_with_each_other). 
    Check about_list_fold_left_and_append_v0_aux.
    rewrite -> (about_list_fold_left_and_append_v0_aux V W nil_case cons_case (reverse_v0_aux V (v' :: vs')) (v :: nil)).
    rewrite -> (IHvs' v' nil_case) at 1.
    rewrite -> (IHvs' v' nil_case).
     rewrite -> (fold_unfold_list_fold_left_cons V
                                                 W
                                                 (cons_case v'
                                                            (list_fold_left V W nil_case cons_case (reverse_v0_aux V vs')))
                                                 (cons_case) v nil).
     Check (fold_unfold_list_fold_left_nil).
     rewrite -> (fold_unfold_list_fold_left_nil V
                                                W
                                                (cons_case v (cons_case v' (list_fold_left V W nil_case cons_case (reverse_v0_aux V vs'))))
                                               cons_case).
reflexivity.     
Qed.

Theorem list_fold_right_in_terms_of_list_fold_left_and_reverse_v0 :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (vs : list V),
    list_fold_left V W nil_case cons_case (reverse_v0 V vs) =
    list_fold_right V W nil_case cons_case vs.
Proof.
  unfold reverse_v0.
  intros V W nil_case cons_case vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_aux_nil V).
    rewrite -> (fold_unfold_list_fold_left_nil V W nil_case cons_case).
    rewrite -> (fold_unfold_list_fold_right_nil V W nil_case cons_case).
    reflexivity.
  - rewrite -> (about_list_fold_left_and_reverse_v0_aux V W nil_case cons_case v vs').
    rewrite -> (fold_unfold_list_fold_right_cons V W nil_case cons_case v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

Theorem list_fold_left_in_terms_of_list_fold_right_and_reverse_v0 :
  forall (V W : Type)
         (v : V)
         (vs : list V),
  forall  (nil_case : W)
          (cons_case : V -> W -> W),
    list_fold_right V W nil_case cons_case (reverse_v0 V (vs)) =
    list_fold_left V W nil_case cons_case (vs).
Proof.
  intros V W v vs.
  intros nil_case cons_case.
  assert (H_involutory := reverse_is_involutory).
  assert (H_right_rev_left := list_fold_right_in_terms_of_list_fold_left_and_reverse_v0).
  Check (H_involutory V vs).
  Check (H_right_rev_left V W  nil_case cons_case (reverse_v0 V vs)).
  rewrite <- (H_right_rev_left V W nil_case cons_case (reverse_v0 V vs)).
  rewrite -> (H_involutory V vs).
  reflexivity.
Qed. 

(*
   m. implement list_fold_left using list_fold_right, without using reverse
 *)

(*

Fixpoint list_fold_right_aux (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    cons_case v (list_fold_right_aux V W nil_case cons_case vs')
  end.
==========================

Fixpoint list_fold_left_aux (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    list_fold_left_aux V W (cons_case v nil_case) cons_case vs'
  end.

--------------------------

  match vs with
  | nil =>
    (fun nil_case => nil_case)
  | v :: vs' =>
    (fun nil_case => (cons_case v nil_case)) 
 
--------------------------
 
 list_fold_right
    (fun nil_case => nil_case)
    (fun ih nil_case => ih (cons_case v nil_case))
    vs nil_case.

--------------------------
nil_case for fold left is the same nil_case for fold_right; so there is no change.
for fold_left is list_fold_left_aux V W (cons_case v nil_case) cons_case vs'
for fold_righ is cons_case v (list_fold_right_aux V W nil_case cons_case vs')
*)
Definition  list_fold_left_in_terms_of_list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs: list V) : W :=
 
 list_fold_right V (W -> W) 
                 (fun nil_case => nil_case)
                 (fun v ih => (fun nil_case => ih (cons_case v nil_case)))
                 vs nil_case.

Lemma fold_unfold_list_fold_left_in_terms_of_list_fold_right_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_left_in_terms_of_list_fold_right V W nil_case cons_case nil = nil_case.
Proof.
  fold_unfold_tactic list_fold_left_in_terms_of_list_fold_right.
Qed.

Lemma fold_unfold_list_fold_left_in_terms_of_list_fold_right_cons :
    forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_left_in_terms_of_list_fold_right V W nil_case cons_case (v :: vs') = list_fold_left_in_terms_of_list_fold_right V W (cons_case v nil_case) cons_case vs'.
Proof.
  fold_unfold_tactic list_fold_left_in_terms_of_list_fold_right.
Qed.


Theorem list_fold_left_in_terms_of_list_fold_right_satisfies_the_specification_of_list_fold_left :
  specification_of_list_fold_left list_fold_left_in_terms_of_list_fold_right.
Proof.
  unfold specification_of_list_fold_left.
  split.
  - exact (fold_unfold_list_fold_left_in_terms_of_list_fold_right_nil).
  - exact (fold_unfold_list_fold_left_in_terms_of_list_fold_right_cons).
Qed.


(*
   l. implement list_fold_right using list_fold_left, without using reverse
 *)

Definition  list_fold_right_in_terms_of_list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs: list V) : W :=

 list_fold_left V (W -> W) 
                  (fun nil_case' => nil_case')
                  (fun v ih => (fun nil_case' => ih (cons_case v nil_case'))) 
                 vs nil_case.
Lemma fold_unfold_list_fold_right_in_terms_of_list_fold_left_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_right_in_terms_of_list_fold_left V W nil_case cons_case nil = nil_case.
Proof.  
  fold_unfold_tactic list_fold_right_in_terms_of_list_fold_left.
Qed.

(*
Lemma fold_unfold_list_fold_right_in_terms_of_list_fold_left_cons :
    forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_right_in_terms_of_list_fold_left V W nil_case cons_case (v :: vs') = cons_case v (list_fold_right_in_terms_of_list_fold_left V W nil_case cons_case vs').
Proof.
  fold_unfold_tactic list_fold_right_in_terms_of_list_fold_left.
Qed.


Theorem list_fold_right_in_terms_of_list_fold_left_satisfies_the_specification_of_list_fold_right :
  specification_of_list_fold_right list_fold_right_in_terms_of_list_fold_left.
Proof.
  unfold specification_of_list_fold_right.
  split.
  - exact (fold_unfold_list_fold_right_in_terms_of_list_fold_left_nil).
  - exact (fold_unfold_list_fold_right_in_terms_of_list_fold_left_cons).
Qed.
*)

Theorem the_grand_finale :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    is_left_permutative V W cons_case ->
    forall (nil_case : W)
           (vs : list V),
      list_fold_left  V W nil_case cons_case vs =
      list_fold_right V W nil_case cons_case vs.
Proof.
  intros V W cons_case.
  intro H_cons_leftp.
  unfold is_left_permutative in H_cons_leftp.
  intro nil_case.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_list_fold_left_nil V W nil_case cons_case).
    rewrite -> (fold_unfold_list_fold_right_nil V W nil_case cons_case).
    reflexivity.
  - Check (fold_unfold_list_fold_left_cons V W nil_case cons_case v vs').
    rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v vs').
    rewrite -> (fold_unfold_list_fold_right_cons V W nil_case cons_case v vs').
    rewrite <- IHvs'.
    Check (finale_eureka V W cons_case H_cons_leftp nil_case v vs').
    exact (finale_eureka V W cons_case H_cons_leftp nil_case v vs').
Qed.

(*
   o. can you think of corollaries of this property?
*)

Lemma plus_is_left_permutative :
  is_left_permutative nat nat plus.
Proof.
  unfold is_left_permutative.
  intros v1 v2 v3.
  Check (Nat.add_assoc).
  rewrite -> (Nat.add_assoc v1 v2 v3).
  rewrite -> (Nat.add_assoc v2 v1 v3).
  Check (Nat.add_comm v1 v2).
  rewrite -> (Nat.add_comm v1 v2).
  reflexivity.
Qed.


Corollary example_for_plus :
  forall ns : list nat,
    list_fold_left nat nat 0 plus ns = list_fold_right nat nat 0 plus ns.
Proof.
  Check (the_grand_finale nat nat plus plus_is_left_permutative 0).
  exact (the_grand_finale nat nat plus plus_is_left_permutative 0).
Qed.

(* What do you make of this corollary?
   Can you think of more such corollaries?
*)

Lemma mult_is_left_permutative :
  is_left_permutative nat nat mult.
Proof.
  unfold is_left_permutative.
  intros v1 v2 v3.
  Check (Nat.mul_assoc).
  rewrite -> (Nat.mul_assoc v1 v2 v3).
  rewrite -> (Nat.mul_assoc v2 v1 v3).
  Check (Nat.mul_comm v1 v2).
  rewrite -> (Nat.mul_comm v1 v2).
  reflexivity.
Qed.

Corollary example_for_mult :
   forall ns : list nat,
    list_fold_left nat nat 0 mult ns = list_fold_right nat nat 0 mult ns.
Proof.
  Check (the_grand_finale nat nat mult mult_is_left_permutative 0).
  exact (the_grand_finale nat nat mult mult_is_left_permutative 0).
Qed.

(*
   p. subsidiary question: does the converse of Theorem the_grand_finale hold?
*)

(*
Theorem the_grand_finale_converse :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    (forall (nil_case : W)
            (vs : list V),
        list_fold_left  V W nil_case cons_case vs =
        fold_right_list V W nil_case cons_case vs) ->
    is_left_permutative V W cons_case.
Proof.
Abort.
*)

(* ********** *)

(* Exercise 8: *)

Fixpoint nat_fold_right (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    s (nat_fold_right V z s n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_right V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_right V z s (S n') =
    s (nat_fold_right V z s n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

(* ***** *)

Fixpoint nat_fold_left (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    nat_fold_left V (s z) s n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_left V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_left V z s (S n') =
    nat_fold_left V (s z) s n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* Exercise 8a *)

Definition nat_nth_rightfold (V : Type) (n : nat) (vs : list V) : option V :=
  nat_fold_right (list V ->  option V)
                 (fun vs => match vs with
                            | nil =>
                              None
                            | v :: vs' =>
                              Some v
                            end)
                 (fun c vs => match vs with
                              | nil =>
                                None
                              | v :: vs' =>
                                c vs'
                              end)
                 n
                 vs.

Compute (test_nat_nth nat_nth_rightfold).

Definition nat_nth_leftfold (V : Type) (n : nat) (vs : list V) : option V :=
  nat_fold_left (list V ->  option V)
                 (fun vs => match vs with
                            | nil =>
                              None
                            | v :: vs' =>
                              Some v
                            end)
                 (fun c vs => match vs with
                              | nil =>
                                None
                              | v :: vs' =>
                                c vs'
                              end)
                 n
                 vs.

Compute (test_nat_nth nat_nth_leftfold).

(* nat_nth_rightfold and nat_nth_leftfold are equivalent *)

(* Exercise 8b *)

Definition list_nth_rightfold (V : Type) (vs : list V) (n : nat) : option V :=
  list_fold_right (V)
                  (nat -> option V)
                  (fun n => None)
                  (fun v c n =>
                     match n with
                     | O =>
                       Some v
                     | S n' =>
                       c n'
                     end)
                  vs
                  n.

Compute (test_list_nth list_nth_rightfold).

Definition list_nth_leftfold (V : Type) (vs : list V) (n : nat) : option V :=
  list_fold_left (V)
                  (nat -> option V)
                  (fun n => None)
                  (fun v c n =>
                     match n with
                     | O =>
                       Some v
                     | S n' =>
                       c n'
                     end)
                  vs
                  n.

Compute (test_list_nth list_nth_leftfold).

(* list_nth_rightfold and list_nth_leftfold are not equivalent *)

(* ********** *)

(* end of midterm-project.v *)
