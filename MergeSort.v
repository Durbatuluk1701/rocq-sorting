(** Sorting Algorithms:*)

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


(** The Algorithms *)


Module InsertionSort.

  Fixpoint insert (x : nat) (l : list nat) : list nat :=
    (* assumes l is already sorted *)
    match l with
    | nil => [x]
    | h :: t => 
      (* find first place where x <= h, 
        thus it can be safely inserted and maintain sortedness
      *)
      if x <=? h then
        x :: l
      else
        h :: insert x t
    end.

  Lemma insert_sorted : forall x l,
    sorted l ->
    sorted (insert x l).
  Proof.
    intros.
    prep_induction H.
    induction H; ff; neqbsimpl; try (econstructor; ff l; fail).
    - econstructor; ff l.
      econstructor.
    - econstructor; ff l.
      econstructor.
    - econstructor; ff.
      pp (IHsorted x); ff; neqbsimpl.
    - econstructor; ff l.
      pp (IHsorted x0); ff; neqbsimpl.
    - econstructor; ff l.
      pp (IHsorted x0); ff; neqbsimpl.
  Qed.

  Lemma insert_count_cons : forall x y l,
    count x (insert y l) = count x l + if Nat.eqb x y then 1 else 0.
  Proof.
    induction l; ff; neqbsimpl; ff.
  Qed.

  Fixpoint insertion_sort (l : list nat) : list nat :=
    match l with
    | nil => nil
    | h :: t => insert h (insertion_sort t)
    end.

  Theorem insertion_sort_correct : sort_correct insertion_sort.
  Proof.
    unfold sort_correct; split; ff.
    - (* sortedness part *)
      induction l; ff.
      * econstructor.
      * eapply insert_sorted; ff.
    - (* counting part *)
      induction l; ff; neqbsimpl; ff.
      * erewrite insert_count_cons; ff l; neqbsimpl.
      * erewrite insert_count_cons; ff l; neqbsimpl.
  Qed.

End InsertionSort.

Module MergeSort.

  Equations merge (l1 l2 : list nat) : list nat by wf (length l1 + length l2) :=
    merge nil l2 := l2;
    merge l1 nil := l1;
    merge (h1 :: t1) (h2 :: t2) :=
      if h1 <=? h2 
      then h1 :: merge t1 (h2 :: t2)
      else h2 :: merge (h1 :: t1) t2.
  Next Obligation.
    lia.
  Defined.

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

  Lemma merge_in : forall l1 l2 x,
    In x (merge l1 l2) <-> In x l1 \/ In x l2.
  Proof.
    intros l1 l2.
    pp (@list_sync_ind nat (fun lp => forall x : nat, In x (merge (fst lp) (snd lp)) <-> In x (fst lp) \/ In x (snd lp))).
    simpl in *.
    specialize H with (lp := (l1, l2)).
    simpl in *.
    eapply H; ff; clear H.
    - ltac1:(autorewrite with merge in * ); destruct l; ff.
    - ltac1:(autorewrite with merge in * ); destruct l; ff.
    - ltac1:(autorewrite with merge in * ); ff.
      * rewrite H1 in H; ff.
      * rewrite H0 in H; ff.
      Show Proof.
      Print Assumptions merge_equation_3.
    - ltac1:(autorewrite with merge in * ); ff.
      * erewrite H1; ff.
      * erewrite H0; ff.
  Qed.
  Print Assumptions merge_in.

  Theorem merge_sorted : forall l1 l2,
    sorted l1 ->
    sorted l2 ->
    sorted (merge l1 l2).
  Proof.
    intros l1 l2.
    pp (@list_sync_ind nat (fun lp => sorted (fst lp) -> sorted (snd lp) -> sorted (merge (fst lp) (snd lp)))).
    simpl in *.
    specialize H with (lp := (l1, l2)).
    simpl in *.
    eapply H; ff; clear H.
    - destruct l; ff.
    - pps H1, H2. 
      erewrite sorted_spec in H1, H2; ff.
      pp (H0 H H5).
      pp (H3 H6 H4).
      clear H0 H3.
      ltac1:(autorewrite with merge).
      ff; neqbsimpl;
      erewrite sorted_spec; split; ff.
      * erewrite merge_in in *; ff a, l.
      * erewrite merge_in in *; ff.
        break_or_hyp.
        + lia.
        + eapply H1 in H0; ff l.
  Qed.

  Theorem merge_count : forall l1 l2 x,
    count x (merge l1 l2) = count x (l1 ++ l2).
  Proof.
    intros l1 l2.
    pp (@list_sync_ind nat (fun lp => forall x : nat, count x (merge (fst lp) (snd lp)) = count x (fst lp ++ snd lp))).
    simpl in *.
    specialize H with (lp := (l1, l2)).
    simpl in *.
    eapply H; ff; clear H.
    - destruct l. 
      * ltac1:(autorewrite with merge in * ); ff.
      * ltac1:(autorewrite with merge in * ); rewrite app_nil_r; ff.
    - ltac1:(autorewrite with merge in * ); ff; neqbsimpl.
      erewrite H0; ff;
      repeat (erewrite count_app); ff l; neqbsimpl.
    - ltac1:(autorewrite with merge in * ); ff; neqbsimpl;
      erewrite H0; ff; neqbsimpl; ff;
      repeat (erewrite count_app); ff l; neqbsimpl.
  Qed.

  Fixpoint split_at_n (l : list nat) (n : nat) : list nat * list nat :=
    match n with
    | 0 => (nil, l)
    | S n' =>
      match l with
      | nil => (nil, nil)
      | h :: t => 
        let '(l, r) := split_at_n t n' in
        (h :: l, r)
      end
    end.

  Lemma split_at_n_zero : forall l,
    snd (split_at_n l 0) = l.
  Proof.
    destruct l; ff.
  Qed.

  Lemma split_at_n_length : forall l,
    fst (split_at_n l (length l)) = l.
  Proof.
    induction l; ff.
  Qed.

  Lemma split_at_n_length_same : forall l n,
    length (fst (split_at_n l n)) + length (snd (split_at_n l n)) = length l.
  Proof.
    induction l; ff.
    pp (IHl n0).
    ff.
  Qed.

  Lemma fst_split_at_n_length_lt : forall l n,
    n < length l ->
    length (fst (split_at_n l n)) = n.
  Proof.
    induction l; ff l.
    assert (n0 < length l) by lia.
    eapply IHl in H0.
    ff.
  Qed.

  Lemma snd_split_at_n_length_lt : forall l n,
    n < length l ->
    length (snd (split_at_n l n)) = length l - n.
  Proof.
    induction l; ff l.
    assert (n0 < length l) by lia.
    eapply IHl in H0.
    ff.
  Qed.

  Lemma split_at_n_rejoin : forall l n,
    l = (fst (split_at_n l n) ++ snd (split_at_n l n)).
  Proof.
    induction l; ff.
    erewrite IHl; rewrite Heqp; ff.
  Qed.

  Lemma add_n_div_n : forall n m,
    0 < n ->
    (n + m) / n = 1 + (m / n).
  Proof.
    intros.
    pp (Nat.div_add_l 1 n m).
    simpl in *.
    erewrite (Nat.add_0_r) in *.
    ff l.
  Qed.

  Lemma n_div : forall n,
    n / 2 < S n.
  Proof.
    intros.
    Search (_ / _ < _).
    pp (Nat.div_lt (S n) 2).
    (* assert (n / 2 <= S n / 2) by admit. *)
    eapply Nat.lt_le_trans > [ | eapply H; lia ].
    clear H.
    pp (Nat.Div0.div_le_mono n (S n) 2).
    assert (n <= S n) by lia.
    eapply H in H0.
    clear H.
    lia.
  Qed.

  Show Obligation Tactic.
  Local Obligation Tactic := idtac.

  Equations merge_sort (l : list nat) : list nat by wf (length l) :=
    merge_sort nil := nil;
    merge_sort [h] := [h];
    merge_sort v := 
      merge (merge_sort (fst (split_at_n v (length v / 2)))) (merge_sort (snd (split_at_n v (length v / 2)))).
  Next Obligation.
    intros.
    subst v.
    erewrite fst_split_at_n_length_lt.
    - assert (length (n :: n0 :: l) = 2 + (length l)) by ff.
      erewrite H.
      erewrite add_n_div_n in *.
      pp (n_div (length l)).
      lia.
      lia.
    - assert (length (n :: n0 :: l) = 2 + (length l)) by ff.
      erewrite H.
      erewrite add_n_div_n in *.
      pp (n_div (length l)).
      lia.
      lia.
  Defined.
  Next Obligation.
    intros.
    subst v.
    erewrite snd_split_at_n_length_lt.
    - assert (length (n :: n0 :: l) = 2 + (length l)) by ff.
      erewrite H.
      erewrite add_n_div_n in *.
      pp (n_div (length l)).
      lia.
      lia.
    - assert (length (n :: n0 :: l) = 2 + (length l)) by ff.
      erewrite H.
      erewrite add_n_div_n in *.
      pp (n_div (length l)).
      lia.
      lia.
  Defined.

  Theorem merge_sort_correct : sort_correct merge_sort.
  Proof.
    unfold sort_correct; split; ff.
    - (* sorting part *)
      (* here is a hacky way to get strong induction! *)
      assert (forall n : nat, forall l : list nat, length l < n -> sorted (merge_sort l)). {
        clear l.
        induction n; ff.
        - destruct l; ff l.
        - destruct l.
          * ltac1:(autorewrite with merge_sort).
            econstructor.
          * destruct l.
            ** ltac1:(autorewrite with merge_sort).
              econstructor.
            ** ltac1:(autorewrite with merge_sort).
              eapply merge_sorted; eapply IHn.
              (* Some non-trivial (but definitely true) arithmetic stuff *)
              + erewrite fst_split_at_n_length_lt.
                -- assert (length (n0 :: n1 :: l) = 2 + (length l)) by ff.
                    erewrite H0.
                    erewrite add_n_div_n in *.
                    pp (n_div (length l)).
                    lia.
                    lia.
                -- assert (length (n0 :: n1 :: l) = 2 + (length l)) by ff.
                    erewrite H0.
                    erewrite add_n_div_n in *.
                    pp (n_div (length l)).
                    lia.
                    lia.
              + erewrite snd_split_at_n_length_lt.
                -- assert (length (n0 :: n1 :: l) = 2 + (length l)) by ff.
                  erewrite H0.
                  erewrite add_n_div_n in *.
                  pp (n_div (length l)).
                  lia.
                  lia.
                -- assert (length (n0 :: n1 :: l) = 2 + (length l)) by ff.
                  erewrite H0.
                  erewrite add_n_div_n in *.
                  pp (n_div (length l)).
                  lia.
                  lia.
      }
      eapply H with (n := S (length l)).
      lia.
    - (* counting part *)
      assert (forall n : nat, forall x l, length l < n -> count x l = count x (merge_sort l)). {
        clear x l.
        induction n; ff.
        - destruct l; ff l.
        - destruct l.
          * ltac1:(autorewrite with merge_sort).
            econstructor.
          * destruct l.
            ** ltac1:(autorewrite with merge_sort).
              econstructor.
            ** ltac1:(autorewrite with merge_sort).
              erewrite merge_count.
              erewrite count_app.
              repeat (erewrite <- IHn).
              erewrite <- count_app.
              pp (split_at_n_rejoin (n0 :: n1 :: l)).
              erewrite <- H0; ff.
              (* Same non-trivial arith as above *)
              + erewrite snd_split_at_n_length_lt.
                -- assert (length (n0 :: n1 :: l) = 2 + (length l)) by ff.
                  erewrite H0.
                  erewrite add_n_div_n in *.
                  pp (n_div (length l)).
                  lia.
                  lia.
                -- assert (length (n0 :: n1 :: l) = 2 + (length l)) by ff.
                  erewrite H0.
                  erewrite add_n_div_n in *.
                  pp (n_div (length l)).
                  lia.
                  lia.
             + erewrite fst_split_at_n_length_lt.
                -- assert (length (n0 :: n1 :: l) = 2 + (length l)) by ff.
                    erewrite H0.
                    erewrite add_n_div_n in *.
                    pp (n_div (length l)).
                    lia.
                    lia.
                -- assert (length (n0 :: n1 :: l) = 2 + (length l)) by ff.
                    erewrite H0.
                    erewrite add_n_div_n in *.
                    pp (n_div (length l)).
                    lia.
                    lia.
      }
      eapply H with (n := S (length l)).
      lia.
  Qed.

  Print Assumptions merge_sort_correct.

End MergeSort.


Module BubbleSort.

  (*

  Local Obligation Tactic := 
    simpl in *; Tactics.program_simplify;
    CoreTactics.equations_simpl;
    try Tactics.program_solve_wf.

  Program Fixpoint list_ind_two {A : Type} (P : list A -> Prop) 
      (fnil : P nil)
      (fsingle : forall x, P [x]) 
      (fcons_two : forall x y l, P (x :: l) /\ P (y :: l) -> P (cons x (cons y l))) (l : list A) {measure (length l)} : P l :=
    match l with
    | nil => fnil
    | [x] => fsingle x
    | x :: y :: l => 
      fcons_two x y l (conj 
        (list_ind_two P fnil fsingle fcons_two (x :: l)) 
        (list_ind_two P fnil fsingle fcons_two (y :: l)))
    end.
  Next Obligation.
    eapply measure_wf.
    eapply well_founded_ltof.
  Qed.

  Equations bubble_up (l : list nat) : list nat by wf (length l) :=
  bubble_up nil := nil;
  bubble_up (cons x nil) := (cons x nil);
  bubble_up (cons x (cons y t)) :=
        (* x < y, so we are good *)
        if Nat.leb x y then
          x :: bubble_up (y :: t)
        else
          (* x >= y, so we need to swap *)
          y :: bubble_up (x :: t).

  Ltac2 Notation "neqbsimpl" :=
    try (rewrite Nat.eqb_eq in * ); ff;
    try (rewrite Nat.eqb_neq in * ); ff;
    try (rewrite Nat.ltb_irrefl in * ); ff.

  Lemma bubble_up_count_invariant : forall l, 
    forall x, count x l = count x (bubble_up l).
  Proof.
    induction l using @list_ind_two; intros.
    - ltac1:(autorewrite with bubble_up); ff.
    - ltac1:(autorewrite with bubble_up); ff.
    - ltac1:(autorewrite with bubble_up); ff;
      neqbsimpl.
      all: try (rewrite <- H; ff; neqbsimpl).
      all: try (rewrite <- H0; ff; neqbsimpl).
  Qed.

  Lemma bubble_up_in_same : forall l,
    forall x, In x l <-> In x (bubble_up l).
  Proof.
    induction l using @list_ind_two; intros.
    - ltac1:(autorewrite with bubble_up); ff.
    - ltac1:(autorewrite with bubble_up); ff.
    - ltac1:(autorewrite with bubble_up); ff;
      neqbsimpl.
      all: try (rewrite <- H in *; ff; neqbsimpl).
      all: try (rewrite <- H0 in *; ff; neqbsimpl).
  Qed.

  Fixpoint min (l : list nat) : option nat :=
    match l with
    | nil => None
    | h :: t =>
      match min t with
      | None => Some h
      | Some v => Some (Nat.min h v)
      end
    end.

  Lemma bubble_up_sorted_invariant : forall l,
    sorted l ->
    sorted (bubble_up l).
  Proof.
    induction l using @list_ind_two; ff.
    ltac1:(autorewrite with bubble_up).
    invc H0.
    pp (H1 H6).
    erewrite <- Nat.leb_le in *.
    ff.
    clear H H1.
    erewrite sorted_spec in *; ff.
    split; ff.
    erewrite Nat.leb_le in *.
    erewrite H4.
    clear H4.
    erewrite <- bubble_up_in_same in *.
    simpl in *; ff.
  Qed.

  Lemma bubble_up_sorted_cons : forall l,
    sorted l ->
    forall h, sorted (bubble_up (h :: l)).
  Proof.
    induction l using @list_ind_two; ff.
    - ltac1:(autorewrite with bubble_up); econstructor.
    - ltac1:(autorewrite with bubble_up); ff; econstructor;
      neqbsimpl; ff.
      * erewrite Nat.leb_le in *; ff.
      * erewrite Nat.leb_gt in *; ff l.
      * econstructor.
    - ltac1:(autorewrite with bubble_up).
      invc H0.
      pp (H1 H6).
      erewrite <- Nat.leb_le in *.
      ff; clear H H1;
      erewrite Nat.leb_le in *.
      * erewrite sorted_spec in *; ff.
        split; ff l.
        + admit.
        + admit.
    

  Compute (bubble_up [3;2;1]).

  (* Now, we need to do n passes of the bubble-up procedure! *)

  Fixpoint do_n_times {A : Type} (f : A -> A) (l : A) (n : nat) : A :=
    match n with
    | 0 => l
    | S n' => f (do_n_times f l n')
    end.

  Lemma do_n_times_invariants : forall {A : Type} (P : A -> Prop) f a n,
    (forall a', P a' -> P (f a')) ->
    P a ->
    P (do_n_times f a n).
  Proof.
    induction n; ff.
  Qed.

  Definition bubble_sort (l : list nat) : list nat :=
    do_n_times bubble_up l (length l).

  Example test1 : bubble_sort [3;2;1;0] = [0;1;2;3].
  Proof. reflexivity. Qed.

  Example test2 : bubble_sort [5;1;4;2;8] = [1;2;4;5;8].
  Proof. reflexivity. Qed.

  Example test3 : bubble_sort [3;3;2;1;4;4] = [1;2;3;3;4;4].
  Proof. reflexivity. Qed.

  (* Now, time to prove correctness! *)

  Theorem bubble_sort_correct : sort_correct bubble_sort.
  Proof.
    unfold sort_correct; intros.
    split.
    - (* is it sorted! *)
      induction l; unfold bubble_sort in *; simpl.
      * econstructor.
      * eapply do_n_times_invariants.
        admit.
        admit.
    - (* does it have the same counts! *)
      unfold bubble_sort.
      eapply do_n_times_invariants; ff.
      erewrite H.
      eapply bubble_up_count_invariant.

  *)
End BubbleSort.