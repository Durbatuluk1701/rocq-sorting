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
  induction l; ff.
  invc H; ff.
  eapply IHl in H3.
  destruct l; ltac1:(simp bubble_up in *).
  - econstructor; ff; eauto using sorted.
  - destruct (a <=? n) eqn:?; ff l; eauto using sorted.
    * erewrite Nat.leb_le in *.
      econstructor; ff; erewrite <- bubble_up_in_same in *; ff.
    * econstructor; ff.
      + erewrite <- bubble_up_in_same in *; 
        erewrite Nat.leb_nle in *; ff l.
        pp (H2 n (or_introl eq_refl)); ff.
      + erewrite Nat.leb_nle in *; ff l.
        pp (H2 n (or_introl eq_refl)); ff.
Qed.

Lemma bubble_up_sorted_cons : forall l,
  sorted l ->
  forall h, sorted (bubble_up (h :: l)).
Proof.
  induction l; ff; ltac1:(simp bubble_up in *);
  invc H; ff; eauto using sorted.
  - econstructor; ff; eauto using sorted.
  - eapply IHl in H3.
    econstructor; ff; eauto using sorted.
    erewrite Nat.leb_le in *.
    erewrite <- bubble_up_in_same in *; ff l.
    eapply H2 in H0; ff l.
  - eapply IHl in H3.
    econstructor; ff; eauto using sorted.
    erewrite Nat.leb_nle in *.
    erewrite <- bubble_up_in_same in *; ff l.
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