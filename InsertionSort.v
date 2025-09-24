From Sorting Require Import SortingHeader.

(** Sorting Algorithms:*)


(** The Algorithms *)


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
