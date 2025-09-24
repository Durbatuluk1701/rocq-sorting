From Stdlib Require Import List Arith.
From Sorting Require Import Tactics.
From Corelib Require Import Program.Wf.
From Equations Require Import Equations.

Import ListNotations.

(* Today we will be covering sorting algorithms and proving their correctness. 

First, we must define what it means for a list to be sorted. We will use the following abstract definition: "a list is sorted if each element is less than or equal to the next element in the list."
*)

Inductive sorted : list nat -> Prop :=
(* The empty list is sorted *)
| sorted_nil : sorted []
(* A single-element list is sorted *)
| sorted_singleton : forall x, sorted [x]
(* If the head "x" is less than or equal to the head of "y :: l" (i.e. "y"), and "y :: l" is sorted, then the whole list is sorted *)
| sorted_cons : forall x y l, 
    x <= y -> 
    sorted (y :: l) -> 
    sorted (x :: y :: l).

Theorem sorted_spec : forall h t,
  sorted (h :: t) <-> ((forall x, In x t -> h <= x) /\ sorted t).
Proof.
  split; ff.
  - prep_induction H.
    induction H; ff.
    * split; ff.
      econstructor.
    * pp (IHsorted _ _ eq_refl).
      clear IHsorted.
      ff.
      split; ff.
      pp (H1 _ H4).
      lia.
  - prep_induction H0.
    induction H0; ff.
    * econstructor.
    * econstructor; ff.
      econstructor.
    * assert (sorted (x :: y :: l)). {
        econstructor; ff.
      }
      econstructor; ff.
Qed.


(* We have established what it means to be sorted, but further we need to establish an overall theorem of "correctness" for a sorting algorithm.
It is not simply enough to say that the output list is sorted; we must also ensure that the output list is a permutation of the input list.

While this is certainly viable, I want to do something a little simpler than fully defining "permutation" here. 
Instead, we will define a function that "counts the occurrences of an element in a list", and then we will prove that the count of each element in the input list is the same as the count of that element in the output list.
*)

Fixpoint count (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | h :: t => if Nat.eqb x h then S (count x t) else count x t
  end.

Lemma count_app : forall x l1 l2,
  count x (l1 ++ l2) = count x l1 + count x l2.
Proof.
  induction l1; destruct l2; ff l.
Qed.

Program Fixpoint list_sync_ind_same {A : Type} (P : (list A * list A) -> Prop) 
    (f_nil_l : forall r, P (nil, r))
    (f_nil_r : forall l, P (l, nil))
    (f_cons  : forall h1 h2 t1 t2, P (t1, t2) -> P (h1 :: t1, h2 :: t2))
    (lp : (list A * list A))
    {measure (length (fst lp) + length (snd lp))}
    : P lp :=
  match lp with
  | (nil, r) => f_nil_l r
  | (l, nil) => f_nil_r l
  | (h1 :: t1, h2 :: t2) => 
    f_cons h1 h2 t1 t2 
      (list_sync_ind_same P f_nil_l f_nil_r f_cons (t1, t2))
  end.
Next Obligation.
  lia.
Qed.
Next Obligation.
  eapply measure_wf.
  eapply well_founded_ltof.
Qed.

Program Fixpoint list_sync_ind {A : Type} (P : (list A * list A) -> Prop) 
    (f_nil_l : forall r, P (nil, r))
    (f_nil_r : forall l, P (l, nil))
    (f_cons  : forall h1 h2 t1 t2, P (h1 :: t1, t2) /\ P (t1, h2 :: t2) -> P (h1 :: t1, h2 :: t2))
    (lp : (list A * list A))
    {measure (length (fst lp) + length (snd lp))}
    : P lp :=
  match lp with
  | (nil, r) => f_nil_l r
  | (l, nil) => f_nil_r l
  | (h1 :: t1, h2 :: t2) => 
    f_cons h1 h2 t1 t2 
      (conj 
        (list_sync_ind P f_nil_l f_nil_r f_cons (h1 :: t1, t2))
        (list_sync_ind P f_nil_l f_nil_r f_cons (t1, h2 :: t2))
      )
  end.
Next Obligation.
  lia.
Qed.
Next Obligation.
  eapply measure_wf.
  eapply well_founded_ltof.
Qed.

(* As a bonus lemma, we could prove this notion equivalent to that of a permutation: all permutations of a list have the same element counts <=> all lists with the same element counts are permutations of each other. *)
Inductive permutation : list nat -> list nat -> Prop :=
| perm_nil: permutation [] []
| perm_skip x l l' : permutation l l' -> permutation (x::l) (x::l')
| perm_swap x y l : permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' :
    permutation l l' -> permutation l' l'' -> permutation l l''.

Lemma perm_refl : forall l,
  permutation l l.
Proof.
  induction l; ff; econstructor; ff.
Qed.

Lemma perm_sym : forall l1 l2,
  permutation l1 l2 ->
  permutation l2 l1.
Proof.
  intros.
  induction H; try (econstructor; ff; fail).
Qed.

Lemma perm_app_l : forall l l1 l2,
  permutation l1 l2 ->
  permutation (l ++ l1) (l ++ l2).
Proof.
  induction l; ff.
  econstructor.
  ff.
Qed.

Lemma perm_app : forall l1 l2 l3 l4,
  permutation l1 l2 ->
  permutation l3 l4 ->
  permutation (l1 ++ l3) (l2 ++ l4).
Proof.
  intros.
  prep_induction H.
  induction H; ff.
  - econstructor; ff.
  - econstructor.
    eapply perm_swap.
    econstructor.
    econstructor.
    eapply perm_app_l.
    ff.
  - 
    pp (IHpermutation1 l3 l4 H1).
    pp (IHpermutation2 l4 l4 (perm_refl l4)).
    eapply perm_trans; ff.
Qed.

Lemma perm_cons : forall l x,
  permutation (x :: l) (l ++ x :: nil).
Proof. 
  induction l; ff.
  - eapply perm_refl.
  - eapply perm_trans with (l' := (a :: x :: l)).
    * eapply perm_swap.
    * econstructor; ff.
Qed.

Lemma perm_app_flip : forall l1 l2,
  permutation (l1 ++ l2) (l2 ++ l1).
Proof.
  induction l1; ff.
  - rewrite app_nil_r. eapply perm_refl.
  - eapply perm_trans with (l' := (a :: (l2 ++ l1))).
    * econstructor; ff.
    * rewrite app_comm_cons.
      assert (l2 ++ a :: l1 = (l2 ++ [a]) ++ l1). {
        rewrite <- app_assoc.
        ff.
      }
      rewrite H.
      eapply perm_trans with (l' := ([a] ++ l2) ++ l1).
      + simpl. eapply perm_refl.
      + eapply perm_app > [ | eapply perm_refl ].
        simpl.
        eapply perm_trans.
        eapply perm_cons.
        eapply perm_refl.
Qed.

Lemma perm_app_cons : forall l1 l2 x,
  permutation (l1 ++ x :: l2) (x :: l1 ++ l2).
Proof.
  intros.
  rewrite app_comm_cons.
  eapply perm_trans.
  eapply perm_app_flip.
  ff.
  econstructor.
  eapply perm_app_flip.
Qed.

Lemma perm_nil_iff_nil : forall l,
  permutation nil l <-> l = nil.
Proof.
  split; ff.
  - prep_induction H.
    induction H; ff l.
    erewrite IHpermutation2; ff.
  - econstructor.
Qed.

Lemma perm_same_length : forall l1 l2,
  permutation l1 l2 -> length l1 = length l2.
Proof.
  ff; induction H; ff l.
Qed.

Lemma count_in : forall l x,
  count x l > 0 <-> In x l.
Proof.
  split; induction l; ff l; neqbsimpl; ff.
Qed.

Lemma same_count_same_length : forall l1 l2, 
  (forall x : nat, count x l1 = count x l2) ->
  length l1 = length l2.
Proof.
  assert (forall n, forall l1 l2, length l1 + length l2 < n -> 
      (forall x : nat, count x l1 = count x l2) -> length l1 = length l2). {
    induction n; ff l.

    destruct l1, l2; ff l; neqbsimpl; ff.
    - pp (H0 n0); ff l; neqbsimpl.
    - pp (H0 n0); ff l; neqbsimpl.
    - pp (H0 n0); pp (H0 n1); ff l; neqbsimpl.
      * erewrite IHn; ff l; pp (H0 x); ff; neqbsimpl.
      * 
        assert (count n0 l2 > 0) by lia.
        assert (count n1 l1 > 0) by lia.
        erewrite count_in in *.
        eapply in_split in H3.
        eapply in_split in H4.
        ff.
        repeat (erewrite length_app in * ); ff l; neqbsimpl; ff.
        f_equal.
        repeat (erewrite count_app in * ); ff l; neqbsimpl; ff.
        repeat (setoid_rewrite count_app in H0).
        ff.
        repeat (rewrite Nat.add_succ_r in * ).
        repeat (rewrite <- length_app).
        erewrite IHn; ff.
        + repeat (erewrite length_app); ff l.
        + repeat (erewrite count_app).
          pp (H0 x3); ff l; neqbsimpl.
  }
  intros.
  eapply H; ff l.
Qed.

Lemma count_permutation : forall l1 l2,
  permutation l1 l2 <-> (forall x, count x l1 = count x l2).
Proof.
  split; ff.
  - prep_induction H.
    induction H; ff.
  - 
    (* ltac1:(generalize dependent H). *)
    assert (forall n, forall l1 l2, length l1 + length l2 < n -> 
        (forall x : nat, count x l1 = count x l2) -> permutation l1 l2). {
      clear l1 l2 H.
      induction n; ff l.
    
      destruct l1, l2; ff l; neqbsimpl; ff.
      - econstructor.
      - pp (H0 n0); ff l; neqbsimpl.
      - pp (H0 n0); ff l; neqbsimpl.
      - pp (H0 n0); pp (H0 n1); ff l; neqbsimpl.
        * econstructor. eapply IHn; ff l; pp (H0 x); ff; neqbsimpl.
        * 
          assert (count n0 l2 > 0) by lia.
          assert (count n1 l1 > 0) by lia.
          erewrite count_in in *.
          eapply in_split in H3.
          eapply in_split in H4.
          ff.
          assert (permutation (x ++ x0) (x1 ++ x2)). {
            eapply IHn; ff l.
            repeat (rewrite length_app in * ).
            ff l.
            pp (H0 x3); ff; neqbsimpl;
            repeat (rewrite count_app in * );
            simpl in *; ff l; neqbsimpl; ff.
          }
          rewrite app_comm_cons.
          rewrite app_comm_cons.
          eapply perm_trans.
          eapply perm_app_flip.
          ff.
          econstructor.
          eapply perm_trans.
          eapply perm_app_flip.
          eapply perm_sym.
          eapply perm_trans.
          eapply perm_app_flip.
          ff.
          econstructor.
          eapply perm_trans.
          eapply perm_app_flip.
          eapply perm_sym.
          ff.
    }
    intros.
    eapply H0; ff.
Qed.


(* Now we can define what it means for a sorting algorithm to be correct. *)
Definition sort_correct (sort : list nat -> list nat) : Prop :=
  forall l, 
    (* The output of "sort" must be "sorted" *)
    sorted (sort l) /\ 
    (* The output of "sort" must have the same element counts as the input *)
    (forall x, count x l = count x (sort l)).
