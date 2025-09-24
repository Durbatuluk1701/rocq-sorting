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