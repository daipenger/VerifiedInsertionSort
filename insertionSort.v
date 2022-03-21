Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Bool.
 
(* ----- Definition of insertion sort ----- *)
 
(* Inserts integer i into the list l, as part of insertion sort.
isSorted l should hold. *)
Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
    nil => [n]
  | head :: tail => if n <=? head then n :: l else head :: insert n tail
  end.
 
(* Insertion sort of list l *)
Fixpoint sort (l : list nat) : list nat :=
  match l with
    nil => nil
  | head :: tail => insert head (sort tail)
  end.
 
(* Example test *)
Compute sort [10;8;3;5;6;7;1;2;4;9].
 
(* ----- Definition of sorted lists ----- *)
 
Fixpoint isSorted (l : list nat) : Prop :=
  match l with
    | nil => True
    | [x] => True
    | x :: ((y :: _) as tail) => x <= y /\ isSorted tail
  end.
 
(* ----- Definition of permutations ----- *)
 
Fixpoint count (x : nat) (l : list nat) : nat :=
  match l with
    nil => 0 |
    head :: tail => if x =? head then S (count x tail) else count x tail
  end.
 
Definition isPermutation (l1 l2 : list nat) :=
forall x : nat, count x l1 = count x l2.
 
(* ----- Proof of sortedness ----- *)
 
(* Insertion of an element keeps a sorted list still sorted *)
Lemma insert_keepsListSorted: forall x : nat, forall l : list nat,
isSorted l -> isSorted (insert x l).
Proof.
intros x l H. induction l; simpl.
  - trivial.
  - case_eq (x <=? a); intros; simpl.
    + apply Nat.leb_le in H0. split.
      * trivial.
      * assumption.
    + apply Nat.leb_gt in H0. destruct l; simpl.
      * lia.
      * firstorder. case_eq (x <=? n).
        ** intro. firstorder.
           *** lia.
           *** apply Nat.leb_le. assumption.
        ** firstorder. replace (n :: insert x l) with (insert x (n :: l)).
           *** assumption.
           *** simpl. case_eq (x <=? n); intro; simpl.
             **** absurd ((x <=? n) = true); auto. rewrite <- not_false_iff_true in H4. auto.
             **** trivial.
Qed.
 
Theorem sort_createsSortedness : forall l : list nat, isSorted (sort l).
Proof.
intros l. induction l.
  - compute. trivial.
  - simpl. apply insert_keepsListSorted. trivial.
Qed.
 
(* ----- Proof of permutation ----- *)
 
Lemma insert_sameXIncreasesCount:
forall x : nat, forall l : list nat, count x (insert x l) = S (count x l).
Proof.
intros x l.
induction l.
  - simpl. rewrite Nat.eqb_refl. trivial.
  - simpl. case_eq (x <=? a); intro; simpl.
    + replace (x =? x) with true. trivial. rewrite Nat.eqb_refl. trivial.
    + case_eq (x =? a); intro; simpl; rewrite IHl; trivial.
Qed.
 
Lemma insert_differentXDoesNotChangeCount:
forall x y : nat, forall l : list nat, (x =? y) = false -> count x (insert y l) = count x l.
Proof.
intros x y l H0. induction l; simpl.
  - rewrite H0. trivial.
  - case_eq (x =? a); intro; simpl.
    + case (y <=? a); simpl.
      * rewrite H0. rewrite H. trivial.
      * rewrite H. rewrite IHl. trivial.
    + case_eq (y <=? a); intro; simpl.
      * rewrite H0. rewrite H. trivial.
      * rewrite H. rewrite IHl. trivial.
Qed.
 
Theorem sort_createsPermutation: forall l : list nat, isPermutation l (sort l).
Proof.
intros l.
induction l; simpl; intro.
  - reflexivity.
  - simpl. case_eq (x =? a); intro; simpl.
    + replace a with x.
      * rewrite insert_sameXIncreasesCount. rewrite IHl. trivial.
      * apply Nat.eqb_eq. assumption.
    + rewrite insert_differentXDoesNotChangeCount.
      * rewrite IHl. trivial.
      * assumption.
Qed.
 
(* ----- Full definition of total correctness ----- *)
 
(* Beware that sort is defined structurally inductive on lists and it is primitive recursive.
In Coq's calculus of inductive constructions, sort is terminating.*)
Theorem sort_correctness: forall l : list nat,
isPermutation l (sort l) /\ isSorted (sort l).
Proof.
intros l. split.
  - apply sort_createsPermutation.
  - apply sort_createsSortedness.
Qed.