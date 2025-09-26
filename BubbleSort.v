From Sorting Require Import SortingHeader.

Local Obligation Tactic := 
  simpl in *; Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try Tactics.program_solve_wf.

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
    econstructor.
  - 
    assert (sorted (x :: l)). {
      repeat (erewrite sorted_spec in *; ff).
    }
    assert (sorted (y :: l)). {
      repeat (erewrite sorted_spec in *; ff).
    }
    pp (H H2).
    clear H.
    pp (H1 H3).
    clear H1.
    setoid_rewrite bubble_up_equation_3 in H.
    setoid_rewrite bubble_up_equation_3 in H4.
    ltac1:(autorewrite with bubble_up in * ).
    ff l; neqbsimpl.
    * econstructor; ff.
      pp (H x); ff l; neqbsimpl.
    * 
      assert (y <= x) by ff l.
      erewrite sorted_spec in H0; ff l.
      pp (H0 y (or_introl eq_refl)); ff l.
    * assert (x <= h <= y) by ff l.
      pp (bubble_up_sorted_invariant _ H3).
      repeat (erewrite sorted_spec; split; ff l);
      clear H H4;
      repeat (erewrite sorted_spec in *; ff l);
      erewrite <- bubble_up_in_same in *; ff l.
      erewrite Heqb0.
      ff l.
    * pp (H4 h); ff l; neqbsimpl.
      pp (H h); ff l; neqbsimpl.
      econstructor; ff.
      invc H0; ff l.
Qed.

Compute (bubble_up [4; 3;2;1]).
Compute (bubble_up [3;2;1; 4]).
Compute (bubble_up [2;1;3; 4]).

(* Now, we need to do n passes of the bubble-up procedure! *)

Fixpoint bubble_sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => 
    let l' := bubble_sort t in
    bubble_up (h :: l')
  end.

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
    induction l; ff.
    * econstructor.
    * eapply bubble_up_sorted_cons; ff.
  - (* does it have the same counts! *)
    induction l; ff; neqbsimpl.
    * erewrite <- bubble_up_count_invariant; ff l; neqbsimpl.
    * erewrite <- bubble_up_count_invariant; ff l; neqbsimpl.
Qed.