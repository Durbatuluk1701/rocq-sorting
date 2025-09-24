From Sorting Require Import SortingHeader.

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